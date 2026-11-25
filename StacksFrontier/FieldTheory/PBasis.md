# Powers of an element whose p-th power lies in a subfield

Module `StacksFrontier.FieldTheory.PBasis`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves one lemma. Let p be a prime, K a field of characteristic p and Mf a subfield of K. For y in K with yᵖ ∈ Mf and y ∉ Mf, `linearIndependent_pow_of_pow_mem_of_notMem` says that 1, y, …, yᵖ⁻¹ are linearly independent over Mf. Since the Frobenius map is injective, yᵖ has no p-th root in Mf, so Xᵖ − yᵖ is irreducible over Mf and is the minimal polynomial of y; the powers below p form the power basis of Mf[y].

The module docstring describes p-bases and p-independence of a field extension and their criteria in terms of Kähler differentials (Tag 07P2); none of these definitions or results is in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/FieldTheory/PBasis.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 54 declarations of the source file 1 are kept. The 53 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 5 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
