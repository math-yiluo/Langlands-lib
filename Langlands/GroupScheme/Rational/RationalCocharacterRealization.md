# Integral realizations of rational cocharacter directions

This is an internal structural construction for the rational parabolic gallery
in Task 5515. A rational direction of a split torus `A` is a rational linear
functional on `ℚ ⊗[ℤ] characterLattice A`. Evaluation at an actual character is
a rational linear form on this space of directions. The existing
`rationalCocharacterEvaluation`, imported from `RelativeReflectionPairing`,
sends an actual integral cocharacter to its pairing functional.

An `IntegralRealization v` retains a positive integer multiplier and an actual
integral cocharacter whose pairings are that multiple of `v`. The published
`IsSplitTorus.exists_positive_multiple_pairing` supplies this data. Positivity
preserves zero, nonnegative and positive pairings.

The chosen realizations define actual subgroup functors `parabolic` and
`centralizer`. In a smooth connected affine group over a field, the published
actual-root containment criterion identifies parabolic containment with
implication of the nonnegative root supports. The published zero-root
containment theorem identifies centralizers with equal zero supports. These
comparisons prove independence of the chosen positive integral realization,
agreement with every original integral cocharacter, and constancy of the
parabolic on each strict sign chamber. The arbitrary split torus is not
assumed maximal in the ambient group.

Every regular rational direction has centralizer equal to the centralizer
of the whole split torus, by the published generic-cocharacter theorem.
Conversely, an integral cocharacter with that full torus centralizer has
nonzero pairing with every actual root. The converse takes a nonzero root
weight vector with zero pairing, places it in the Lie kernel of the
cocharacter centralizer using the dynamic Lie theorem, and then places it in
the zero torus weight space using equality of centralizers. Disjointness of
distinct split-torus weight spaces gives a contradiction. This also proves
regularity of the associated rational endpoint. No self-centralizing or
maximal-torus hypothesis is used in this converse.

The proof uses only the imported published structural results and elementary
ordered rational arithmetic. It claims no new result from the external
representation-theoretic literature. It does not construct actual rank-one
wall models or prove either gallery existence target or the final
irreducible-induced-twist proposition; those remain separate obligations.
