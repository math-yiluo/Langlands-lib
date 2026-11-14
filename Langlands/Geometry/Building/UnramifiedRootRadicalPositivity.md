# Radical root points and nearby parabolic model comparisons

Author: Worker 200.

This internal bridge combines the integral-point transfer in
`RadicalPreimageTransfer` with the strict-positivity criterion in
`UnramifiedRootTranslationPositivity`. It works at arbitrary universe `u`,
over a local domain `R` with fraction field `k`, a field extension `K/k`,
and a smooth affine `k`-group `G`. The lower torus `S` is split. As in the
translation criterion, an upper apartment `D` for `T_K` in `G_K`, a map
`f : S → T`, splitness of `T_K`, and upper opposite-factor pairs are supplied.

Let `target` be actual `RelativeComponentModelData R k G`, let
`iS : S → G` be the lower torus homomorphism, and let `x` belong to `D`.
The Prop-valued definition
`KPApartmentData.ParabolicRootComparisonsNearDescentTranslations` requires
the following for every lower torus vector `v` and every real `t` sufficiently
near zero:

- An actual source model and a compatible model morphism from it to `target`
  exist.
- The morphism has parabolic schematic image on neutral special fibres
  and satisfies the exact reduction-preimage equality.
- Every source integral point belonging to a lower relative root group has
  nonnegative restricted root value at the actual upper apartment point
  `D.descentTranslate f hS x (t • v)`.

The neighbourhood can depend on `v`. The source and its morphism can depend
on both `v` and `t`. For each such pair they compare every lower relative
root and every rational point of its root group. Only the implication from
integrality to nonnegativity is required.

Let `Q` be supplied special-fibre quotient data for `target` whose radical
inclusion is the actual ground-field unipotent radical. A reductive quotient
property for its projection is not required. The implemented theorems prove:

- `nonnegativeNearDescentTranslations_of_mem_positivePoints`: a root-group
  point in `Q.positivePoints` has nonnegative restricted root value along
  each sufficiently small descended translation line.
- `strictPositive_of_mem_positivePoints_of_parabolicRootComparisons`: its
  restricted root value at `x` is strictly positive.
- `not_mem_positivePoints_of_eq_zero_of_parabolicRootComparisons`: a
  root-group point with restricted value zero lies outside `Q.positivePoints`.

Here `Q.positivePoints` retains its definition as the generic image of
integral sections reducing to rational points of the represented radical.

## Implemented proof and provenance

For each nearby parameter the supplied parabolic image, exact
reduction-preimage equality, and represented radical give
`Q.positivePoints ≤ source.neutral.integralPoints` by
`RelativeComponentModelHom.positivePoints_le_source_of_parabolicReductionPreimage`.
The source root comparison therefore gives nonnegativity at the translated
upper point. Applying this implication inside the neighbourhood filter
proves the first theorem.

A relative root is a nonzero character by `mem_relativeRoots`. The
equivalence
`KPApartmentData.strictPositive_iff_nonnegativeNearDescentTranslations`
then gives the second theorem. Strict positivity contradicts value zero,
giving the third.

These are derived consequences of the two imported helpers and the
published relative-root definition. No axiom for a root valuation on the
restricted family, including V5, is used. The assertions hold for arbitrary
upper points; coefficient-fixedness and an unramified field extension are
unnecessary for this implication.

## Remaining obligations

This module supplies a conditional implication. It does not construct the
target or source models, their morphisms, their parabolic and preimage
properties, or the root comparisons. In the fixed-point application,
coefficient-fixedness of `x` ensures that its descended translations are
also fixed, by `galois_fixed_descentTranslate`.

The implication from strictly positive root value to membership in the
radical preimage is neither required nor asserted. For the depth-zero
opposite-factor argument one must still construct the nearby model data,
prove the integral root comparison at the initial point, supply an integral
split torus and a reductive quotient, and prove the integral opposite-factor
theorem. The unconditional target remains open.
