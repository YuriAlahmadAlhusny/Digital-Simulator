/*
 * Copyright (c) 2018 Helmut Neemann.
 * Use of this source code is governed by the GPL v3 license
 * that can be found in the LICENSE file.
 */
package de.neemann.digital.hdl.vhdl2;

import de.neemann.digital.hdl.printer.CodePrinterStr;
import de.neemann.digital.integration.ToBreakRunner;
import junit.framework.TestCase;

public class VHDLGeneratorTest extends TestCase {

    public void testComb() throws Exception {
        ToBreakRunner br = new ToBreakRunner("dig/hdl/model2/comb.dig");
        CodePrinterStr out = new CodePrinterStr();
        new VHDLGenerator(br.getLibrary(), out).export(br.getCircuit());

        assertEquals("-- generated by Digital. Don't modify this file!\n" +
                "-- Any changes will be lost if this file is regenerated.\n" +
                "\n" +
                "LIBRARY ieee;\n" +
                "USE ieee.std_logic_1164.all;\n" +
                "\n" +
                "entity DIG_D_FF is\n" +
                "  generic (\n" +
                "    Default: std_logic ); \n" +
                "  port ( D  : in std_logic;\n" +
                "         C  : in std_logic;\n" +
                "         Q  : out std_logic;\n" +
                "         notQ : out std_logic );\n" +
                "end DIG_D_FF;\n" +
                "\n" +
                "architecture Behavioral of DIG_D_FF is\n" +
                "   signal state : std_logic := Default;\n" +
                "begin\n" +
                "   Q    <= state;\n" +
                "   notQ <= NOT( state );\n" +
                "\n" +
                "   process(C)\n" +
                "   begin\n" +
                "      if rising_edge(C) then\n" +
                "        state  <= D;\n" +
                "      end if;\n" +
                "   end process;\n" +
                "end Behavioral;\n" +
                "\n" +
                "\n" +
                "LIBRARY ieee;\n" +
                "USE ieee.std_logic_1164.all;\n" +
                "USE ieee.numeric_std.all;\n" +
                "\n" +
                "entity main is\n" +
                "  port (\n" +
                "    A: in std_logic;\n" +
                "    B: in std_logic;\n" +
                "    C: in std_logic;\n" +
                "    X: out std_logic;\n" +
                "    Y: out std_logic;\n" +
                "    Z: out std_logic;\n" +
                "    Aident: out std_logic);\n" +
                "end main;\n" +
                "\n" +
                "architecture Behavioral of main is\n" +
                "  signal Y_temp: std_logic;\n" +
                "  signal s0: std_logic;\n" +
                "  signal Z_temp: std_logic;\n" +
                "begin\n" +
                "  Y_temp <= (B OR NOT C);\n" +
                "  Z_temp <= NOT A;\n" +
                "  s0 <= ((A OR C) AND (Z_temp OR C) AND '1' AND NOT (B OR C) AND Y_temp);\n" +
                "  gate0: entity work.DIG_D_FF\n" +
                "    generic map (\n" +
                "      Default => '0')\n" +
                "    port map (\n" +
                "      D => s0,\n" +
                "      C => '1',\n" +
                "      Q => X);\n" +
                "  Y <= Y_temp;\n" +
                "  Z <= Z_temp;\n" +
                "  Aident <= A;\n" +
                "end Behavioral;\n",out.toString());
    }

    public void testSplitter3() throws Exception {
        ToBreakRunner br = new ToBreakRunner("dig/hdl/model2/splitter3.dig");
        CodePrinterStr out = new CodePrinterStr();
        new VHDLGenerator(br.getLibrary(), out).export(br.getCircuit());

        assertEquals("-- generated by Digital. Don't modify this file!\n" +
                "-- Any changes will be lost if this file is regenerated.\n" +
                "\n" +
                "LIBRARY ieee;\n" +
                "USE ieee.std_logic_1164.all;\n" +
                "USE ieee.numeric_std.all;\n" +
                "\n" +
                "entity main is\n" +
                "  port (\n" +
                "    A: in std_logic_vector(3 downto 0);\n" +
                "    B: in std_logic_vector(3 downto 0);\n" +
                "    S: out std_logic_vector(3 downto 0));\n" +
                "end main;\n" +
                "\n" +
                "architecture Behavioral of main is\n" +
                "begin\n" +
                "  S(1 downto 0) <= (A(1 downto 0) AND B(1 downto 0));\n" +
                "  S(3 downto 2) <= (A(3 downto 2) OR B(3 downto 2));\n" +
                "end Behavioral;\n",out.toString());
    }

    public void testSplitter2() throws Exception {
        ToBreakRunner br = new ToBreakRunner("dig/hdl/model2/splitter2.dig");
        CodePrinterStr out = new CodePrinterStr();
        new VHDLGenerator(br.getLibrary(), out).export(br.getCircuit());

        assertEquals("-- generated by Digital. Don't modify this file!\n" +
                "-- Any changes will be lost if this file is regenerated.\n" +
                "\n" +
                "LIBRARY ieee;\n" +
                "USE ieee.std_logic_1164.all;\n" +
                "USE ieee.numeric_std.all;\n" +
                "\n" +
                "entity main is\n" +
                "  port (\n" +
                "    A: in std_logic_vector(1 downto 0);\n" +
                "    B: in std_logic_vector(1 downto 0);\n" +
                "    X: out std_logic;\n" +
                "    Y: out std_logic_vector(2 downto 0));\n" +
                "end main;\n" +
                "\n" +
                "architecture Behavioral of main is\n" +
                "  signal s0: std_logic_vector(3 downto 0);\n" +
                "begin\n" +
                "  s0(1 downto 0) <= A;\n" +
                "  s0(3 downto 2) <= B;\n" +
                "  X <= s0(0);\n" +
                "  Y <= s0(3 downto 1);\n" +
                "end Behavioral;\n",out.toString());
    }

    public void testSplitter2I() throws Exception {
        ToBreakRunner br = new ToBreakRunner("dig/hdl/splitter2.dig");
        CodePrinterStr out = new CodePrinterStr();
        new VHDLGenerator(br.getLibrary(), out).export(br.getCircuit());

        assertEquals("-- generated by Digital. Don't modify this file!\n" +
                "-- Any changes will be lost if this file is regenerated.\n" +
                "\n" +
                "LIBRARY ieee;\n" +
                "USE ieee.std_logic_1164.all;\n" +
                "USE ieee.numeric_std.all;\n" +
                "\n" +
                "entity main is\n" +
                "  port (\n" +
                "    inst: in std_logic_vector(15 downto 0);\n" +
                "    n9SD: out std_logic_vector(15 downto 0));\n" +
                "end main;\n" +
                "\n" +
                "architecture Behavioral of main is\n" +
                "  signal s0: std_logic;\n" +
                "begin\n" +
                "  s0 <= inst(8);\n" +
                "  n9SD(7 downto 0) <= inst(7 downto 0);\n" +
                "  n9SD(8) <= s0;\n" +
                "  n9SD(9) <= s0;\n" +
                "  n9SD(10) <= s0;\n" +
                "  n9SD(11) <= s0;\n" +
                "  n9SD(12) <= s0;\n" +
                "  n9SD(13) <= s0;\n" +
                "  n9SD(14) <= s0;\n" +
                "  n9SD(15) <= s0;\n" +
                "end Behavioral;\n", out.toString());
    }

    public void testSkip() throws Exception {
        ToBreakRunner br = new ToBreakRunner("dig/hdl_skip/skipOuter.dig");
        CodePrinterStr out = new CodePrinterStr();
        new VHDLGenerator(br.getLibrary(), out).export(br.getCircuit());

        assertEquals("-- generated by Digital. Don't modify this file!\n" +
                "-- Any changes will be lost if this file is regenerated.\n" +
                "\n" +
                "LIBRARY ieee;\n" +
                "USE ieee.std_logic_1164.all;\n" +
                "USE ieee.numeric_std.all;\n" +
                "\n" +
                "entity main is\n" +
                "  port (\n" +
                "    A: in std_logic;\n" +
                "    B: in std_logic;\n" +
                "    Y: out std_logic);\n" +
                "end main;\n" +
                "\n" +
                "architecture Behavioral of main is\n" +
                "  signal s0: std_logic;\n" +
                "begin\n" +
                "  gate0: entity work.skipInner\n" +
                "    port map (\n" +
                "      i => B,\n" +
                "      o => s0);\n" +
                "  Y <= (A AND s0);\n" +
                "end Behavioral;\n", out.toString());
    }

    public void testNames() throws Exception {
        ToBreakRunner br = new ToBreakRunner("dig/hdl_names/main.dig");
        CodePrinterStr out = new CodePrinterStr();
        new VHDLGenerator(br.getLibrary(), out).export(br.getCircuit());

        assertEquals("-- generated by Digital. Don't modify this file!\n" +
                "-- Any changes will be lost if this file is regenerated.\n" +
                "\n" +
                "LIBRARY ieee;\n" +
                "USE ieee.std_logic_1164.all;\n" +
                "USE ieee.numeric_std.all;\n" +
                "\n" +
                "entity a_b is\n" +
                "  port (\n" +
                "    A: in std_logic;\n" +
                "    B: in std_logic;\n" +
                "    Y: out std_logic);\n" +
                "end a_b;\n" +
                "\n" +
                "architecture Behavioral of a_b is\n" +
                "begin\n" +
                "  Y <= (A AND B);\n" +
                "end Behavioral;\n" +
                "\n" +
                "LIBRARY ieee;\n" +
                "USE ieee.std_logic_1164.all;\n" +
                "USE ieee.numeric_std.all;\n" +
                "\n" +
                "entity main is\n" +
                "  port (\n" +
                "    A: in std_logic;\n" +
                "    B: in std_logic;\n" +
                "    Y: out std_logic);\n" +
                "end main;\n" +
                "\n" +
                "architecture Behavioral of main is\n" +
                "begin\n" +
                "  gate0: entity work.a_b\n" +
                "    port map (\n" +
                "      A => A,\n" +
                "      B => B,\n" +
                "      Y => Y);\n" +
                "end Behavioral;\n", out.toString());
    }

}