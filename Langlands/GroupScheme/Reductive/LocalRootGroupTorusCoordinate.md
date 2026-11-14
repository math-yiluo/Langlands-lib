# Torus-equivariant root parametrizations over arbitrary local rings

This module is an internal derivation from the actual dynamic root subgroup,
its flat polynomial coordinate, the additive-coordinate construction, and the
full-torus weight construction. It removes the reducedness assumption from the
root-parametrization step. It does not prove the full local Isomorphism Theorem.

Let `R` be a commutative ring, `G` an affine group scheme over `Spec R`, and
`i : G_m^I → G` a homomorphism, where `I` is finite. For exponent vectors
`mu, nu`, use the existing actual dynamic group
`Uc i mu nu = U_{Z_G(mu)}(nu)` and its coordinate algebra `coordU`.
All declarations retain universe `u`.

## The actual torus action

`torusAction` is the existing full-torus conjugation action on this dynamic
unipotent group, transported to its corepresented algebra-point functor.
`action_act_comp_incl` proves on every scheme test that its inclusion in `G`
is conjugation by `i(t)`. Its proof composes the existing action identity in
the dynamic centralizer with the inclusion of that centralizer in `G`, and
uses `torusZ_comp` and the affine-model isomorphism.

`charValue_exponentCharacter` computes a fixed-exponent character as the unit
monomial on an arbitrary scheme test. `appTop_act_of_isHomogeneous` applies the
corepresented homogeneous-coordinate identity and the existing comparison with
scheme points. Consequently, `coordX_act_of_isHomogeneous` says that the
coordinate of the acted-on point is the character value times its coordinate.

`rootMap_equivariant_of_isHomogeneous` assumes a polynomial coordinate `x`
with bijective evaluation, an additive coordinate identity on every test,
and homogeneity of weight `a` for the actual torus action. Bijectivity of the
coordinate shows that acting on the point with parameter `c` gives the point
with parameter `a(t)c`. Composing with the actual root-group inclusion proves
torus equivariance of `rootMap` on every scheme test. This argument imposes
no reducedness or locality condition on the base ring.

## Identifying the exponent vector

`charValue_torusPt` computes the character value at prescribed affine unit
coordinates, after the canonical global-sections comparison for `Spec A`.
`exponent_eq_of_field_charValues` assumes that `R` is local and that two
integer exponent vectors have equal character values at every field-valued
torus point over `R`. It proves equality of the exponent vectors as follows.
Take the residue field `k`, the domain `D = k[I → Z]`, and its fraction field
`K`. The independent invertible monomials in `D`, mapped to `K`, define a torus
point. The two character values are the images of the corresponding monomials.
Injectivity of `D → K` and injectivity of a nonzero monomial's exponent index
then give equality of the exponent vectors. The domain property uses the
unique-sums structure on `I → Z` and the field coefficients.

This auxiliary field distinguishes integer vectors. It is not used to detect
equality of morphisms over `R`; all-scheme action identities were proved
before this separation argument, so the argument retains nilpotents in `R`.

`HasEquivariantFibres i mu nu a` is the proposition that for every field
`K` over `R`, the actual base change `UK` has an isomorphism from `Ga K` whose
composite with the inclusion in the dynamic centralizer is equivariant for
the fixed exponent character `a`, on every scheme test over `K`.

`isHomogeneous_of_equivariantFibres` assumes a local base, a positive degree
`d`, a degree-`d` polynomial coordinate with bijective evaluation,
`sum j, a j * nu j = d`, and `HasEquivariantFibres`. The full-torus weight
construction first supplies some weight `m`. On each field fibre, the existing
Laurent-scaling coefficient calculation shows that the image of `x` in `K[X]`
is a scalar times `X`. The existing field-equivariance lemma therefore gives
weight `a` for the same root map. Compare it with the all-scheme weight-`m`
identity at parameter `1`. The root map is a closed immersion and hence a
monomorphism; scalar points are injective. Cancellation gives equality of the
two character values. The preceding exponent-separation lemma proves `m = a`,
which establishes homogeneity for the prescribed root.

## Actual root parametrizations

`exists_isRootParametrization_of_flat` additionally assumes `G` smooth,
`sum j, a j * mu j = 0`, and the positive pairing and fibre data above.
The flat-coordinate theorem supplies the positive homogeneous polynomial
coordinate over the arbitrary local base. The additive-coordinate theorem
makes it additive on every scheme test. The identified weight gives actual
torus equivariance. Finally the existing `isRepresentedBy_rootMap` identifies
the map's range with the actual relative root subgroup; the map is a closed
immersion. These are exactly the three clauses of `IsRootParametrization`.

`rootParametrizationOfFibres` chooses such a map. Its specification is
`isRootParametrization_rootParametrizationOfFibres`. The choice is not claimed
to be canonical.

`exists_rootParametrization_of_flat` specializes this construction to a
reductive `G`, a coordinate split torus that is maximal on every field fibre,
and an actual fibrewise root datum `P`. For every root of `P` it supplies a
root parametrization over `R`. It reuses the existing generic-kernel
cocharacter construction and the field rank-one root-group theorem: choose
`mu` whose orthogonal roots are precisely the chosen root and its negative,
and take `nu` to be its coroot, with pairing `2`. The field root-group theorem
provides exactly `HasEquivariantFibres`.

No reducedness, noetherianity, henselianity, or characteristic hypothesis is
introduced. The remaining local Isomorphism Theorem obligations include Weyl
normalization and compatible big-cell gluing over arbitrary local rings.
