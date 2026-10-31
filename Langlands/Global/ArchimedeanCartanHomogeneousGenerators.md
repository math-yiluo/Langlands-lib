# Finite homogeneous generators of actual compact covariants

Author: Worker 94. This is an internal consequence of actual covariant finiteness
in `ArchimedeanCartanCovariantFiniteness` and the canonical projections in
`ArchimedeanCartanHomogeneousCovariants`. The coefficient ring is the genuine
`lieSymmetricGroupInvariants K n`, acting through actual Cartan restriction.
Covariants are the fixed tensors for the full standard compact subgroup in
the actual complementary symmetric algebra tensored with `τ`.

`HomogeneousCartanCovariantGenerators` records a finite family, a natural
degree for each generator, homogeneity with respect to the canonical tensor
projections, and the equality of its span over the full-group invariant
coefficient ring with the whole covariant module. Zero generators, repeated
degrees and an empty family are permitted; there is no independence claim.

For every number field in an arbitrary universe, every natural rank and every
`τ : ContinuousCompactRep K n`,
`nonempty_homogeneousCartanCovariantGenerators` constructs such a family.
First, module finiteness supplies finitely many possibly inhomogeneous
generators. Split each into its finite canonical degree decomposition. The
finite dependent family of all these components contains a decomposition of
each old generator, so its span is the whole module. Reindex this family by a
finite ordinal. `homogeneousCartanCovariantGenerators` chooses one such
family.

`HomogeneousCartanCovariantGenerators.exists_homogeneous_coefficients` provides
degree control, in addition to ordinary module finiteness. For a homogeneous
covariant `x` of degree `d`, it gives a coefficient expression
`x = ∑ i, c i • generator i` in which `c i` is a genuine full-group invariant
homogeneous of degree `d - degree i`. If `degree i > d`, that coefficient is
zero. To prove this, take any coefficient expression from the spanning
property and project onto degree `d`. Projection of each summand selects
exactly the complementary coefficient component; components with excessive
generator degree disappear. This coefficient-selection theorem itself
requires only a field and a given homogeneous generating family, without a
number-field assumption.

This module proves finite homogeneous generation and exact coefficient
degrees on the actual symmetric covariants. Filtered transfer to the genuine
enveloping center and the final automorphic differential-growth theorem
remain separate obligations.
