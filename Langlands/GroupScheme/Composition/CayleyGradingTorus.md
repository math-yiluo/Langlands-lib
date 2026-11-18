# Split tori in Cayley automorphism group schemes from lattice gradings

Author: Worker 118.

Let `c : CayleyDatum K` over a field `K`, in any characteristic. Let
`iH : H ⟶ GL₈` satisfy `c.IsAutomorphismRepresentation iH`, and let
`g : c.Grading (I → ℤ)` be a grading (module
`Langlands.GroupScheme.Composition.CayleyGrading`) whose support generates
`ℤ^I`. This module constructs a closed split torus `𝔾ₘ^I → H` and
concludes `|I| ≤ splitRank H`. The torus acts on the homogeneous component
of degree `m` by the character `t ↦ tᵐ`.

## The extended multiplication as a bilinear map

- `multiplicationOver_comp_self`: for vectors with coefficients in `K`,
  the extended multiplication along `φ : K → A` is the image of the
  product.
- `multiplicationBilin φ`: the extended multiplication
  `c.multiplicationOver φ` packaged as an `A`-bilinear map, with
  `multiplicationBilin_apply`.

## Monomials in units

For `t : I → Aˣ` and `m : I → ℤ`, `monomial t m = ∏ᵢ tᵢ^{mᵢ}`. Its
properties: `monomial_add`, `monomial_zero`, `monomial_neg`,
`monomial_mul` (multiplicative in `t`), `monomial_one`, `monomial_map`
(compatibility with ring maps) and `monomial_single`
(`monomial t (single i 1) = tᵢ`).

## Torus matrices over a coefficient ring

Fix a ring map `φ : K → A` into a commutative ring.

- `projOver φ m` is the projection matrix of degree `m` with coefficients
  mapped along `φ`. The facts `projOver_mul_projOver`, `sum_projOver`,
  `sum_projOver_mulVec`, `projOver_mulVec_comp` and `projOver_projOver`
  carry over from the grading.
- `projOver_multiplicationOver`: over `A`, the product of the degree `a`
  part of `x` and the degree `b` part of `y` has degree `a + b`. Both
  sides are `A`-bilinear in `(x, y)` (via `multiplicationBilin`), so it
  suffices to check basis vectors. These are images of vectors over `K`,
  where the statement is `Grading.proj_mul`.
  `multiplicationOver_eq_zero`: such a product vanishes when `a + b` is
  outside the support.
- `torusMatrix φ t = ∑ₘ tᵐ • projOver φ m` (sum over the support), with
  `torusMatrix_mulVec`, `torusMatrix_mul`
  (`torusMatrix t * torusMatrix s = torusMatrix (t s)`) and
  `torusMatrix_one`. `torusUnit φ : (I → Aˣ) →* GL (Fin 8) A` is the
  resulting group homomorphism, with `torusUnit_val`. `torusMatrix_map`
  and `torusUnit_map` give compatibility with further ring maps.
- `isAutomorphismMatrix_torusUnit`: every `torusUnit φ t` is an
  automorphism matrix in the sense of `CayleyDatum.IsAutomorphismMatrix`.
  It fixes the unit, which has degree `0`, and `t⁰ = 1`. To see that it
  preserves the extended product, expand `x` and `y` into homogeneous
  parts. On the product of the parts of degrees `a` and `b` the matrix
  acts by `t^{a+b} = tᵃ tᵇ`, or the product is zero when `a + b` is
  outside the support.
- `torusUnit_injective`: if the support generates `ℤ^I`, then
  `torusUnit φ` is injective. If `torusMatrix t = torusMatrix s`, multiply
  by `projOver φ m` and compare a nonzero entry, which is a unit since
  `K` is a field. This gives `tᵐ = sᵐ` for every `m` in the support. The
  set of `m` with `tᵐ = sᵐ` is a subgroup, so it is everything, and
  `monomial_single` gives `t = s`.

## The split torus in the automorphism group scheme

- `sectionsMap T` is the structure map `K → Γ(T)` of a test scheme `T`
  over `Spec K`. `sectionsMap_naturality` is its naturality.
- `isRepresentedBy_range hrep`: the range subfunctor of `iH` is
  represented by `iH`, which is a monomorphism since it is a closed
  immersion.
- `torusRangePoints hrep T` sends a `T`-point of `𝔾ₘ^I` (coordinates
  `t ∈ Γ(T)ˣ^I`) to `torusUnit (sectionsMap T) t`. This lies in the range
  of `iH` by the all-test hypothesis `hrep.2` and
  `isAutomorphismMatrix_torusUnit`. `torusPoints hrep T` lifts it to a
  `T`-point of `H`. `torusPoints_comp` and `torusPoints_naturality`
  record that composing with `iH` gives the torus matrix and that the
  construction is natural in `T`. Naturality is checked after composing
  with the monomorphism `iH`.
- `torusHom hrep : splitTorus (Spec K) I ⟶ H` is the homomorphism of
  group schemes defined by these natural points (the Library's
  `homOfPoints`).
- `mono_torusHom`: if the support generates `ℤ^I`, `torusHom` is a
  monomorphism, by `torusUnit_injective` on all test points.
- `isAffineHom_X` and `locallyOfFiniteType_X`: `H` is affine and
  locally of finite type over `K`, because `iH` is a closed immersion
  into `GL₈` (affine, and smooth by the Library's
  `GeneralLinear.smoothStatement`).
- `isClosedSubgroup_torusHom`: `torusHom` is a closed subgroup, by the
  Library theorem `IsTorus.isClosedSubgroup_of_mono` (a monomorphism from
  a torus into an affine group locally of finite type is a closed
  subgroup).

## Main result

**`Grading.card_le_splitRank (hrep) (hgen) : (Nat.card I : ℕ∞) ≤ splitRank H`**
for a grading `g : c.Grading (I → ℤ)` with
`AddSubgroup.closure g.support = ⊤`. This is the Library's
`card_le_splitRank` applied to the closed subgroup `torusHom`.

## Provenance

This is internal, derived content. A grading of an algebra by a
character lattice is the same as an action of the corresponding split
torus by algebra automorphisms. The module makes this explicit at the
level of points over every test scheme, as the all-test hypothesis
`IsAutomorphismRepresentation` requires. No external structural theorem
is used beyond the cited Library results.

The grading evaluates an additive exponent by `splitTorus.exponentValue I t (Multiplicative.ofAdd m)`.
