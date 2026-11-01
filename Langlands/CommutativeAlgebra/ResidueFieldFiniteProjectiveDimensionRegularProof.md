# Regularity from finite projective dimension of the residue field

`Langlands.CommutativeAlgebra.residueFieldFiniteProjectiveDimensionRegular.{u}`
proves exactly
`Langlands.CommutativeAlgebra.ResidueFieldFiniteProjectiveDimensionRegularStatement.{u}`.
For every Noetherian local commutative ring `R : Type u`, existence of a natural
projective-dimension bound for its canonical residue-field module implies
`IsRegularLocalRing R`. The universe is arbitrary, and the theorem has no
additional outer hypotheses.

The proof composes the two published numerical bounds. Writing `κ` for
`ModuleCat.of R (IsLocalRing.ResidueField R)` and `𝔪` for the maximal ideal,
`residueFieldProjectiveDimensionLowerBound R` gives
`𝔪.spanFinrank ≤ CategoryTheory.projectiveDimension κ`. The finiteness
hypothesis permits `residueFieldProjectiveDimensionUpperBound R h`, which gives
`CategoryTheory.projectiveDimension κ ≤ ringKrullDim R`. These comparisons use
the common ordered type `WithBot ℕ∞`, with the natural embedding dimension
coerced into it. Transitivity yields `𝔪.spanFinrank ≤ ringKrullDim R`.
Mathlib's `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` then supplies
regularity, using the general opposite inequality for a Noetherian local ring.
The natural witness in the finiteness hypothesis is unrestricted.

The two bound theorems are imported by Lean name from
`Langlands.CommutativeAlgebra.ResidueFieldProjectiveDimensionLowerBoundProof`
(Worker 1211) and
`Langlands.CommutativeAlgebra.ResidueFieldProjectiveDimensionUpperBoundProof`
(Worker 1116). This assembly uses their independently published results and
Mathlib's regularity criterion. Its imports do not use the project's forward
finite-module theorem, localization regularity, or the downstream factoriality
and valuative-extension conclusions.

The argument is implication (1) to (3) in Stacks Project Proposition 10.110.5,
[Tag 00OC](https://stacks.math.columbia.edu/tag/00OC), using Lemmas 10.110.3 and
10.110.4, [Tag 00OA](https://stacks.math.columbia.edu/tag/00OA) and
[Tag 00OB](https://stacks.math.columbia.edu/tag/00OB).
The complete retained pages and comments were read. They are registered as
`stacks-regular-local-homological-2026-11-01` (directory SHA-256
`21820755db776b97fc099941b898e15c3b34a12ac214b637216d74b85046b6fd`)
and `stacks-residue-field-projective-dimension-bounds-2026-11-01`
(directory SHA-256
`40635b9a819b6011c03de10b01cecd53bb1c9e67a82d3022bfa106470bac0743`).
Only the stated implication is proved here.
