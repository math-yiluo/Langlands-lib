# Normalized Jacquet modules of actual parabolic orbit pieces

This module provides internal constructions for the proof of
`PadicParabolicSupportGradedTheorem`. It composes the published covariance,
compact-induction and radical-coinvariant constructions; it asserts no graded
comparison, exactness or modulus cancellation.

`Parabolic.normalizedCoinvariantsFunctor B δ` takes representations of the
parabolic `P_B` itself to representations of its actual product Levi. Its vector
space is the quotient by `u v - v` for the actual unipotent radical. The Levi acts
through the existing section `leviInParabolic`, multiplied by `δ(m)^(-1/2)`.
Morphisms descend the original intertwiner to the quotient. The identity and
composition laws are checked on quotient representatives; the displayed map
lemma says `[v]` maps to `[f(v)]`. This construction uses no extension of the
parabolic representation to the ambient general linear group, and it needs no
smoothness or exactness assumption.

`rawOrbitPiece P Q w` is conjugated restriction along the existing
`stabilizerToInducing`, followed by compact induction from the existing subgroup
`orbitStabilizer P Q w` to `Q`. Its input may be an arbitrary algebraic
representation of `P`. Its output functions have compact support modulo the
stabilizer and an open right stabilizer, by the published compact-induction
construction. The theorem `orbitPiece_eq_rawOrbitPiece` identifies its restriction
to smooth inputs with the published `orbitPiece`, by definition.

For an actual finite p-adic extension with supplied compatible topology,
`parabolicOrbitJacquetFunctor T B C w` first inflates a smooth Levi representation
of `B` and twists it by the positive half of the block modulus. It then forms the
raw compact orbit piece at the permutation matrix of `w`, and takes normalized
radical coinvariants for `P_C`, using the inverse positive half of its block
modulus. The orbit convention is `P_B * w⁻¹ * P_C`; thus its covariance uses
conjugation by `w⁻¹`. Field and representation universes are independent; the
compactly induced carrier has their maximum universe. All smooth complex input
representations are allowed.

The provenance is internal composition of `Parabolic.LeviBridges`,
`Geometric.ClosedSubgroupDefinitions`, and the `inducingFunctor` in
`Geometric.ParabolicSupportFiltration`. No new interpretation of a literature
statement is asserted. Comparison with `geometricPieceFunctor`, including
cancellation of every normalization character, is a separate proof obligation.
