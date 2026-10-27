# Graded comparisons for normalized opposite Jacquet image filtrations

This module states two comparisons for the fixed image filtrations constructed
in `Parabolic.OppositeJacquetFiltration`. All three declarations are
proposition-valued definitions. They specify proof obligations.

## Refined opposite clause

Fix `F : PadicField p`, `T : F.TopologicalData`, an ordered block shape `B`
of rank `n`, and an inner refinement `S`. Equip the field with `T.topology`.
For every complex representation `ρ` of the product Levi `B.Levi F.Carrier`
on a carrier `V`, assume `IsSmooth ρ`. Given any finite
`s : ObjectRepFiltration (Rep.of ρ) l`, write `s_k` for its actual invariant
subspace at index `k : Fin (l + 1)`.

Let `q` be the actual lower-radical coinvariant map
`Geometric.refinedOppositeJacquetMk B S ρ`, and let
`t = T.normalizedRefinedOppositeJacquetFiltration B S ρ s`. Its step
`t_k` is the actual submodule image `q(s_k)`.
`NormalizedRefinedOppositeJacquetFiltrationGradedClause` asserts, for each
original index `i : Fin l`,

```text
Nonempty
  ((t.gradedRepresentation i).ρ.Equiv
    (T.normalizedRefinedOppositeJacquet B S (s.gradedRepresentation i).ρ)).
```

Thus the source is the actual quotient of `q(s_{i+1})` by `q(s_i)`,
with its induced normalized refined-Levi action. The target is the actual
normalized lower-radical coinvariant quotient of the original representation
on `s_{i+1}/s_i`. `Representation.Equiv` requires both a complex-linear
equivalence of these carriers and intertwining of their actions.

## Composed opposite clause

`NormalizedComposedOppositeJacquetFiltrationGradedClause` makes the analogous
assertion for every smooth representation `ρ` of
`GeneralLinear n F.Carrier`. Here the quotient map is
`Parabolic.composedOppositeJacquetMk B S ρ`, the source uses the fixed
`T.normalizedComposedOppositeJacquetFiltration B S ρ s`, and the target is
`T.normalizedComposedOppositeJacquet B S (s.gradedRepresentation i).ρ`.
Both are representations of the published common refined Levi.

In each clause both actions are the existing normalized actions, using
`Jacquet.inverseHalfCharacter` of the corresponding opposite full modulus.
The identities `T.inverseHalf_refinedOppositeLeviModulus B S` and
`T.inverseHalf_composedOppositeLeviModulus B S` identify these characters
with the positive half of the respective upper full modulus. The composed
character retains its full outer and inner factors.

## Quantifiers and provenance

`NormalizedOppositeJacquetFiltrationGradedStatement.{uF,uV}` universally
quantifies the field, topological data, rank, block shape and refinement,
and conjoins the two clauses. The field universe `uF` and representation
carrier universe `uV` are independent. All finite lengths are quantified.
The fixed filtrations preserve their original indices, including repeated
steps and zero graded quotients; zero rank and empty refinements are allowed.
Existence is asserted only for the equivalence of each grade, using
`Nonempty`. No replacement filtration is existentially quantified.

Smoothness of the input representation is the sole additional hypothesis.
There is no admissibility, finite composition length, irreducibility,
splitting, supplied exactness or supplied graded-comparison premise.

This is an internal derived statement, not a transcription of a separately
numbered literature theorem. Its algebraic provenance is ordinary smooth
coinvariant exactness from `Jacquet.ExactProof`, the actual image constructors
in `Parabolic.OppositeJacquetFiltration`, and the scalar-twist and quotient
transport interfaces in `Filtration.TwistGraded` and
`Filtration.ObjectTransport`. Exactness identifies the quotient of adjacent
images with the coinvariants of the original adjacent quotient; scalar
twisting then retains the published normalization. Establishing and applying
the required exactness for both actual radicals remains part of a separate
proof obligation. This module proves no graded comparison, multiplicity
comparison or irreducible-head assertion.
