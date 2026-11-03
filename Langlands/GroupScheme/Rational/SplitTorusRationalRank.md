# Rational character coordinates and intrinsic ranks of split tori

This is derived lattice algebra for the intrinsic rank target. It uses the existing actual group schemes and their full character lattices. It makes no assertion about conjugacy of maximal split tori or a root/character complement.

For an actual splitting `e : T.toGrp ≅ splitTorus (Spec k) I` with finite `I`, `splitTorusCharacterCoordinates e` first regards `e` as an isomorphism of commutative group schemes. The existing `characterLattice.congr` and `splitTorus.characterLatticeEquiv` give an additive equivalence from `characterLattice T` to `I → ℤ`. The definition `splitTorusRationalCharacterCoordinates e` applies the published `RationalSpan.tensorEquivPi` to construct a rational linear equivalence to `I → ℚ`. Its pure-tensor formula records the associated coordinates.

`IsSplitTorus.finite_characterLatticeRat` uses the published finite generation of the integral character lattice and Mathlib's finiteness of scalar extension. Any actual relative root span is a subspace of this finite-dimensional rational space, so `IsSplitTorus.finite_relativeRootSpan` follows without a root-system hypothesis. The separate `IsConnectedReductive.finite_rationalCharactersRat` applies the published `rationalCharacterLattice` theorem and scalar-extension finiteness.

The coordinate equivalence proves `splitTorusRank_eq_card_of_splitting`, including an empty splitting index. This identifies the lattice rank with `IsSplitTorus.rank` and hence with the split rank of the source torus. The last lemma transports the published bound for an embedded split torus to a lower bound on the ambient split rank. Equality with the ambient split rank for maximal split tori remains a separate geometric obligation.

The provenance is internal and derived: the constructions compose the existing lattice equivalences, and the proofs use finite-dimensional linear algebra and the published split-rank comparisons. No additional original-literature assertion is introduced.
