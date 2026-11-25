# Finite type sheaves of modules: quotients

Module `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a sheaf of rings `R` on a site `(C, J)`, the file proves that a quotient of a sheaf of `R`-modules of finite type is of finite type. Finite type is Mathlib's `SheafOfModules.IsFiniteType`.

## Main definitions and results

- `Stacks.SheafOfModules.isFiniteType_of_epi`: if `p : M ⟶ N` is an epimorphism and `M` is of finite type (an explicit hypothesis), then `N` is of finite type.
- `localGeneratorsDataOfEpi σ p`: local generators data of `M` pushed forward along an epimorphism `p : M ⟶ N`; the covering is unchanged and each generating family is replaced by its image. It is of finite type when `σ` is (instance `isFiniteType_localGeneratorsDataOfEpi`).
- `restrictFreeHom f p`: for a morphism `f : W ⟶ V` of the site, the restriction of `p : free I ⟶ M.over V` to a morphism `free I ⟶ M.over W`.

## Watch for

- The results on quotients assume, as instance hypotheses, that every restriction functor `overFunctor R V` preserves colimits, and `HasSheafify` and `WEqualsLocallyBijective` for abelian groups on every slice site. A local instance, `preservesEpimorphisms_overFunctor`, turns the colimit preservation into preservation of epimorphisms; the colimit preservation itself is not derived.
- `restrictFreeHom` assumes binary products and pullbacks in `C`.
- The module docstring describes images, the extension statement of Tag 01B7 and a pointwise criterion for finite type on a topological space; none of these is declared in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FiniteTypeExtension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 37 declarations of the source file 5 are kept. The 32 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 2 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- The one reference to EGA or SGA that the source writes as an attribute of that library was on a declaration left out; none is listed above.
