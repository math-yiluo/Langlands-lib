# The coefficient-matrix criterion for reduced-translation exhaustion

Authors: Worker 1450 (Lean proof and first Markdown draft); Worker 1411
(Markdown revision and submission).

This module proves `matrixUnipotenceConilpotence`, whose type is exactly
`MatrixUnipotenceConilpotenceStatement.{u,v}` from the published module
`Langlands.GroupScheme.CoalgebraUnipotence.Statements`, for independent
universe parameters `u` and `v`:

```
∀ (k : Type u) [Field k] (B : Type v) [Ring B] [Bialgebra k B],
  IsMatrixUnipotent k B ↔ IsLocallyConilpotent k B
```

In words: for every field `k` and every `k`-bialgebra `B`, every
positive-size coefficient matrix (`comul (a i j) = ∑ l, a i l ⊗ₜ a l j`,
`counit (a i j) = δ i j`) has a nonzero vector `v` with
`∑ j, v j • a i j = v i • 1` for all `i` if and only if every element of `B`
lies in some level of the reduced-right-translation filtration
`reducedLevel k B`. No finite-dimensionality, finite-generation,
commutativity or antipode hypothesis on `B` is assumed.

## Proof

The proof introduces the binders of the statement and combines the two
implications proved in the supporting modules:

- [`ConilpotenceFromMatrix`](ConilpotenceFromMatrix.md) proves
  `isLocallyConilpotent_of_isMatrixUnipotent`. Each finite-dimensional
  quotient of a right-translation-stable subspace carries a coefficient
  matrix, built from extended coordinate functionals and lifted basis
  vectors; matrix unipotence then gives a nonzero quotient vector killed by
  all reduced translations. Inside a finite-dimensional stable subspace the
  pulled-back filtration stabilizes by Noetherianity, and such a fixed vector
  modulo a stationary proper level would lie in the next level, so the
  stationary level is the whole subspace. Every element lies in such a
  subspace, namely the span of the entries of a coefficient matrix given by
  the published theorem `AffineLinearEmbedding.exists_matrix_coefficients`.
- [`MatrixFromConilpotence`](MatrixFromConilpotence.md) proves
  `isMatrixUnipotent_of_isLocallyConilpotent`. Among nonzero vectors, choose
  one whose coefficient entries `∑ j, v j • a i j` all lie in the smallest
  possible level. That level is positive, and minimality forces every
  reduced right translation to kill these entries. Separation by linear
  functionals then shows each entry equals its counit `v i` times `1`.

The development check of this module reported only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Provenance

This is an internal criterion relating the two predicates of
`CoalgebraUnipotence.Definitions`; `Statements.md` records its motivation
from Milne's Theorem 14.5 (a) ⇔ (c). The proof is internal and algebraic.
It does not compare `IsMatrixUnipotent` with unipotence of group schemes or
`IsLocallyConilpotent` with Milne's coconnectedness, and it does not follow
Milne's argument.
