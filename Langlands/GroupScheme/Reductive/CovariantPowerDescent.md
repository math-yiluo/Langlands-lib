# Covariance of a coordinate from covariance of a power

This is an internal supporting module for the proof of
`SplitDominantHighestWeightRepresentationsExistStatement`. It is used for the
saturation of realized weights in `SplitBorelCellPower`. If an `n`-th power of a
coordinate is left covariant or right invariant, the coordinate itself is too,
provided the base field is algebraically closed, the relevant tensor product of
coordinate algebras is a domain, and the counits are normalized.

The idea is classical. If `f(hg)^n = (χ(h) f(g))^n` holds identically, then
`f(hg) = ζ(h, g) χ(h) f(g)`, where `ζ` is an `n`-th root of unity varying over a
connected base and is therefore constant. Evaluating at the identity gives
`ζ = 1`. This module states the result for the universal point, where "connected"
becomes "the coordinate ring of the source is a domain". No declaration
formalizes a literature statement.

Throughout, `k : Type u` is a field, and `G`, `H`, `U` are group schemes over
`Spec (CommRingCat.of k)` with affine structure morphisms. `algebra G` is the
chosen coordinate algebra (`AffineCoordinates.algebra`), and `pointAlgebraHom G T g`
evaluates coordinates at a point `g : T ⟶ G.X`. The proof reuses
`productMap_rTensor'` and `productMap_comp_include`, the tensor product-map
identities from `HomogeneousCharacterCoordinates`.

## Scalars between elements with equal powers

`AffineCoordinates.exists_eq_algebraMap_mul_of_pow_eq`: let `k` be an
algebraically closed field, `R` a `k`-algebra that is a domain, `n > 0`, and
`y z : R` with `y ^ n = z ^ n`. Then `y = algebraMap k R ζ * z` for some `ζ : k`.

Proof. If `z = 0`, then `y = 0` and `ζ = 0` works. Otherwise
`w = y / z` in `FractionRing R` satisfies `w ^ n = 1`. So `w` is integral over
`k` (`IsIntegral.of_pow`). Its minimal polynomial is irreducible, so it has degree
one over the algebraically closed field (`IsAlgClosed.degree_eq_one_of_irreducible`).
Hence `w` is the image of a scalar `ζ` (`minpoly.mem_range_of_degree_eq_one`), and
`y = ζ z` follows after clearing the denominator in the fraction field
(`IsFractionRing.injective`).

## Left covariance

`AffineCoordinates.mem_leftCovariantSubspace_of_pow`: assume `k` is algebraically
closed and `algebra H ⊗[k] algebra G` is a domain. Let `i : H ⟶ G`, `χ : algebra H`
and `f : algebra G`, and let `n > 0`. Assume that for every test object `T` and
points `h : T ⟶ H.X`, `g : T ⟶ G.X`,

`pointAlgebraHom G T ((h ≫ i) * g) f ^ n = (pointAlgebraHom H T h χ * pointAlgebraHom G T g f) ^ n`,

and that `χ` and `f` have counit `1`. Then `f ∈ leftCovariantSubspace i χ`.

Proof. The proof follows the Library's
`AffineCoordinates.mem_leftCovariantSubspace_of_points`. Take the universal test
`B = algebra H ⊗[k] algebra G` with the points `algPoint H includeLeft` and
`algPoint G includeRight`. Evaluating the hypothesis there and using that the
spectrum counit of `B` is injective (`counit_unop_injective`) gives
`Y ^ n = Z ^ n` in `B`. Here `Y` is the pullback of the comultiplication of `f`
along `i`, and `Z = χ ⊗ₜ f`. By the first lemma, `Y = ζ • Z` for some scalar `ζ`,
which by `mem_leftCovariantSubspace` says `f ∈ leftCovariantSubspace i (ζ • χ)`.
Evaluating this covariance at the identity point of the identity test scheme
(`pointAlgebraHom_leftCovariant`, `pointAlgebraHom_one_apply`) and using the two
counit conditions gives `ζ = 1`.

## Right invariance

`AffineCoordinates.mem_rightInvariantSubspace_of_pow`: assume `k` is
algebraically closed and `algebra U ⊗[k] algebra G` is a domain. Let `j : U ⟶ G`,
`f : algebra G` with counit `1`, and `n > 0`. Assume
`pointAlgebraHom G T (g * (u ≫ j)) f ^ n = pointAlgebraHom G T g f ^ n` for all
test objects `T` and points `u`, `g`. Then `f ∈ rightInvariantSubspace j`.

Proof. Apply the left-covariance lemma to `antipodeCoord G f` with the trivial
character `1`. Points of the antipode are values at inverses
(`pointAlgebraHom_antipode`), and `(g * (u ≫ j))⁻¹ = (u⁻¹ ≫ j) * g⁻¹`
(`mul_inv_rev`, `GrpObj.inv_comp`). So the hypothesis becomes the power
covariance of `antipodeCoord G f`, whose counit is `1` (evaluate at the identity
point). The resulting left covariance of the antipode, evaluated at `u⁻¹` and
`g⁻¹`, is the right invariance of `f`.
