# Affine-base isomorphism neighbourhoods for split tori

Let `R` be an arbitrary commutative ring, and let `i : H ⟶ G` be a
homomorphism between split tori over `Spec R`. The final theorem
`TorusIsomorphismLocus.exists_open_affine` says that if the base change of
`i` along a specified field-valued point `x : Spec K ⟶ Spec R` is an
isomorphism, there is an open immersion `q : V ⟶ Spec R` and a morphism
`bx : Spec K ⟶ V` with `bx ≫ q = x`, such that the actual group-scheme
base change of `i` to `V` is an isomorphism. The ring, schemes, character
groups and field belong to the arbitrary universe `u`.

The group-scheme forgetful functor reflects isomorphisms:
`isIso_iff_underlying` constructs the inverse group morphism from the
underlying scheme isomorphism, using reflection in the over category.
The tensor-spectrum naturality comparison then identifies isomorphisms of
actual affine base changes with bijectivity of their tensor coordinate maps.
The canonical monoid-algebra scalar equivalences preserve bijectivity.
For diagonal Hopf spectra, this yields
`HopfMorphismBaseChange.isIso_hopf_split_baseChange_iff`, expressed in
the canonical bialgebra scalar coordinates.

`diagonalSource R M` is the spectrum of the standard Hopf algebra `R[M]`,
for an additive commutative group `M`.
`diagonalCoordinateMap` applies full faithfulness of the Hopf-spectrum
functor to the supplied actual diagonal homomorphism. Its Hopf spectrum
is exactly that homomorphism. The lemma `diagonal_iso_iff` applies the
preceding scalar criterion to this coordinate map.

For a bialgebra map `f : R[N] → R[M]` with `N` finitely generated as an
additive monoid, a field-specialized isomorphism supplies a finite
coefficient product `r` whose image in the field is nonzero and whose
invertibility forces bijectivity after any scalar extension. This is the
imported `DiagonalIsomorphismLocus.exists_principal_isomorphism_certificate`.
Taking `V = Spec (Localization.Away r)` makes the coefficient invertible.
The scalar criterion proves that the actual group homomorphism over `V`
is an isomorphism. The localization universal property supplies the lift
of the original field point and proves the exact factorization equality.
No finite-generation hypothesis on `M` is needed for this diagonal step.

For arbitrary split tori `H` and `G`, choose their presentations by
finite products indexed by `I` and `J`. The existing diagonalizable
comparisons identify these with the standard Hopf spectra for `I → ℤ`
and `J → ℤ`. Precomposition and postcomposition by their base-changed
isomorphisms preserve the isomorphism condition. The diagonal
neighbourhood construction therefore gives the claimed neighbourhood
for `i` itself. Finally, the fully faithful spectrum functor writes an
arbitrary supplied affine field point as its actual ring map, which
provides the algebra structure needed by the construction.

This is an internal derivation from the tensor-spectrum comparison,
the finite coefficient certificate, standard diagonalizable presentations,
and the localization universal property. It does not require the base to
be reduced or noetherian. This module establishes affine neighbourhoods;
it does not construct a global isomorphism locus, perform descent for
relative tori, or prove Hom representability.

The standard `diagonalSource` abbreviation reuses
`TorusClosedImmersionLocus.diagonalSource` from `ClosedImmersionLocusAffine`;
both denote the same actual diagonal Hopf spectrum.
