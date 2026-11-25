# Lifting algebraic properties from a closed fibre

Module `StacksFrontier.RingTheory.Flat.LocalCriteria.FibreCriteria`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

These criteria lift injectivity, exactness at one place of a complex and freeness across a local homomorphism R → S of commutative local rings with S Noetherian. Write 𝔪 for the maximal ideal of R.

- `Module.Flat.injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing` gives injectivity and an R-flat cokernel for an R-linear u : N → M with N finite over S and M flat over R, provided N/𝔪N → M/𝔪M is injective.
- `Module.Flat.ker_eq_range_and_flat_quotient_range_of_mem_sup_smul_top` applies it at one index of a complex P → N → M of S-modules, g followed by f, with N finite over S and M flat over R. If f(x) ∈ 𝔪M forces x ∈ 𝔪N + g(P), then Ker f = Im g and M/f(N) is R-flat.
- `Module.Flat.free_and_flat_of_free_maximalIdeal` takes a finite nonzero S-module M flat over R, and assumes R Noetherian as well. If M/𝔪M is free over S/𝔪S, then M is free over S and S is flat over R.

Two public lemmas serve these proofs. `Stacks.Flatness.FibreNonZeroDivisor.mapQ_injective_iff` says that the map M/p → N/q induced by g is injective exactly when g⁻¹(q) ⊆ p. `Module.Flat.injective_mapQ_restrictScalars_of_forall_mem` uses it to test injectivity of the map of R-fibres N/IN → M/IM of an S-linear map on the submodules (IS)N and (IS)M.

The first criterion uses estimates modulo powers of 𝔪 and Krull intersection. The other two apply it to the map out of the quotient by the previous image in a complex, and to lifts of a fibre basis together with Nakayama's lemma.

In the first criterion N has its R-action by restriction through S, and M needs only an R-module structure. The module docstring and the section headings also announce Tags 00MF, 00MG and 00MI, the lifting of a nonzerodivisor, of a regular sequence and of exactness of a complex from the fibre; those results are not in the file.

The first criterion is Tag 00ME and the freeness result Tag 00MH. The table of references below includes EGA III 4.6.7.1 for the first criterion.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00ME](https://stacks.math.columbia.edu/tag/00ME) | `Module.Flat.injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing` | `N/𝔪N` is `N ⧸ 𝔪 • (⊤ : Submodule R N)` and `ū` the canonical `Submodule.mapQ` of `u`. The cokernel `M/u(N)` is `M ⧸ LinearMap.range u`, and the two conclusions are conjoined; see the module docstring. The non-Noetherian generalization is 046Y. |
| [00MH](https://stacks.math.columbia.edu/tag/00MH) | `free_and_flat_of_free_maximalIdeal` | \"Nonzero\" is `Nontrivial M`. The fibre ring is `S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)` and `M/𝔪M` is `M ⧸ 𝔪S • (⊤ : Submodule S M)`, whose `S/𝔪S`-module structure is `Module.instQuotientIdealSubmoduleHSMulTop`. The two conclusions are conjoined, in the source's order: `M` is free over `S`, `S` is flat over `R`. `IsNoetherianRing R` is unused but is part of the tag's hypotheses; see the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | III 4.6.7.1 | `Module.Flat.injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing` |  |
| EGA | 0 10.1.3 | `free_and_flat_of_free_maximalIdeal` | special case |
| EGA | 0 10.2.4 | `_root_.Module.Flat.ker_eq_range_and_flat_quotient_range_of_mem_sup_smul_top` | b ⇒ a |
| EGA | IV 11.3.7 | `_root_.Module.Flat.ker_eq_range_and_flat_quotient_range_of_mem_sup_smul_top` | (b) ⇒ (a), special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/LocalCriteria/FibreCriteria.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 37 declarations of the source file 17 are kept. The 20 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 2 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 4 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
