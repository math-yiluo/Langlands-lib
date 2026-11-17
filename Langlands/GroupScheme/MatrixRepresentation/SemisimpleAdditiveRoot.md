# Semisimplicity excludes additive root actions

This module supplies an internal derived ingredient for the forward implication
of Milne, *Algebraic Groups* (2017), Proposition 12.54, printed pp.248–249
(registered source `milne-2017-algebraic-groups`). It implements the
upper-unitriangular obstruction using the Library's actual group schemes and
all affine test algebras. It does not assert the full characterization of
commutative linearly reductive groups.

Let `k` be any field in universe `u` and `G` any group scheme over `Spec k`.
There is no finite-type, affineness, smoothness, reducedness or commutativity
hypothesis on `G` in this module.

`additiveRootRepresentation f` composes an actual homomorphism
`f : G ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1` with the published
additive root homomorphism into `SL₂` and the published inclusion into `GL₂`.
`additiveRootRepresentation_pointMatrix` identifies its matrices on every
scheme test with the corresponding transvection. The theorem
`additiveRootRepresentation_affineMatrix_eq` identifies its matrix over each
`k`-algebra `A` with `[[1, a], [0, 1]]`, where `a` is precisely the sole raw
affine coordinate of `f` at that point. Its proof transports the scheme-point
formula through the canonical global-sections isomorphism of `Spec A`.
`additiveRootRepresentation_affineMatrix` packages this as an existential
upper-unitriangular formula.

`upperUnipotent_coefficient_eq_zero` applies to any two-dimensional matrix
representation whose matrices have this form over all affine test algebras.
Its other hypothesis says that the supremum of the nonzero simple stable
subspaces is the full coordinate space, with stability defined by the
Library's `IsStableSubspace`. It proves that each upper-right coefficient
vanishes.

The implemented argument first proves that the first coordinate line
`L = k e₀` is stable. If a coefficient `a` is nonzero, linear dual separation
provides a `k`-linear functional `ℓ : A → k` with `ℓ(a) ≠ 0`. For a vector
`v` in a stable subspace, subtracting `ℓ(1) • v` from the coefficient vector
obtained by applying `ℓ` to the action gives `ℓ(a) * v₁ • e₀` in that same
subspace. If `v₁ ≠ 0`, rescaling puts `e₀` in the subspace. A simple stable
subspace containing `L` must equal `L`; therefore every simple stable
subspace lies in `L`. Their supremum cannot contain the second basis vector,
contradicting the semisimplicity hypothesis.

Finally, `additiveRootRepresentation_affineCoordinates_eq_zero` specializes
this argument to the representation induced by `f`. Assuming semisimplicity
only for that representation, it proves that the original additive coordinate
is zero at every point over every affine test algebra. This conclusion is
formulated with `Corepresented.affinePointsEquiv`, so affine morphism
extensionality can use it directly. The proof needs neither primitive-element
machinery nor detection by rational points.
