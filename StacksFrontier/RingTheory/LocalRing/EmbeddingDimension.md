# Embedding dimension and projective dimension

Module `StacksFrontier.RingTheory.LocalRing.EmbeddingDimension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The cotangent space of a Noetherian local ring measures the minimal number of generators of its maximal ideal. This number is bounded by the projective dimension of the residue field.

`IsLocalRing.finrank_cotangentSpace_le_projectiveDimension_residueField` takes a Noetherian local ring R with maximal ideal m and residue field κ. It gives dim over κ of m/m² ≤ pd over R of κ. The comparison is in `WithBot ℕ∞` and permits infinite projective dimension. The residue field is viewed as an object of `ModuleCat` in the universe of R, and Noetherianity makes the cotangent space finite-dimensional.

The proof converts a natural bound d on the projective dimension into a generating set of m with at most d elements. If the residue field is projective, R is a field. A bound of one on its projective dimension makes m a free ideal, hence principal. For the induction, prime avoidance gives a nonzerodivisor x in m outside m² if m is nonzero. The depth-zero argument behind this choice uses a minimal free cover to show that a finite module of finite projective dimension is free when a nonzero element of R is annihilated by m.

The short exact sequence from m to R to κ lowers the projective dimension bound by one on m. Reduction modulo x preserves this bound on m/xm, and a functional on m/m² exhibits the residue field of R/(x) as a direct summand of m/xm. Induction on the bound over R/(x) then gives generators that lift to generators of m together with x.

The inequality is Tag 00OA. The minimal free cover lemma corresponds to part of SGA 6 I 1.3.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00OA](https://stacks.math.columbia.edu/tag/00OA) | `finrank_cotangentSpace_le_projectiveDimension_residueField` | `dim_κ 𝔪/𝔪²` is the `finrank` of `IsLocalRing.CotangentSpace R` over `IsLocalRing.ResidueField R`, and `pd_R κ` is `CategoryTheory.projectiveDimension` of `κ` in `ModuleCat R`, valued in `WithBot ℕ∞`. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 6 I 1.3 | `exists_surjective_forall_mem_maximalIdeal_of_mem_ker` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/LocalRing/EmbeddingDimension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
