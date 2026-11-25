# Quotients of sheaves of modules of finite type

Module `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a site `C` with a sheaf of rings `R`, the file proves that restriction of sheaves of `R`-modules to an object of the site preserves epimorphisms, and that finite type passes to quotients. The declarations are in the namespace `Stacks.SheafOfModules`.

- `over_epi`: when `C` has binary products, the restriction `p.over U` of an epimorphism `p` to an object `U` is an epimorphism.
- `isFiniteType_of_epi'`, `isFiniteType_of_iso`: a quotient of a sheaf of finite type is of finite type; finite type is invariant under isomorphism.

The finite-type results carry instance hypotheses: binary products in `C`, and sheafification of abelian groups on the slice sites, with weak equivalences the locally bijective maps.

## Points to watch

- Everything lives in one universe `u` (site, rings, modules). `isFiniteType_of_epi'` is stated at `IsFiniteType.{u, u, u}` and does not apply when Mathlib's three universes differ.
- `R` need not be commutative.
- The module docstring describes the coherence predicate, the category `Coh(𝒪_X)` and further closure results, citing Tags 01BV and 01BY; none of these is declared in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Coherent.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 27 declarations of the source file 3 are kept. The 24 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 2 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- The 2 references to EGA and SGA that the source writes as attributes of that library were on declarations left out; none is listed above.
