# Finite algebra maps give finite Banach chart maps on analytifications

This module is internal infrastructure for the proof that affine
analytification detects quasi-finite maps (`AffineAnalytificationQuasiFiniteProof`). Let `K` be a complete, ultrametric,
nontrivially normed field. Let `A` and `B` be commutative `K`-algebras with
finite polynomial presentations `P` and `Q`, and let `f : A →ₐ[K] B`. The
module shows the following. If `f` is module-finite, then over each original
chart of `Spec(A)ᵃⁿ` the induced map of analytifications is given by one
saturated chart of `Spec(B)ᵃⁿ`, and the corresponding bounded algebra map is
finite in Berkovich's Banach sense (`BoundedAlgHom.IsFiniteBanach`). The
statement is the affine-chart form of the standard fact that a finite
morphism of affinoid algebras is finite in the sense of Berkovich. No external
source passage is formalized here, and no premise is introduced. The algebraic
input is Mathlib's integrality of module-finite maps. The analytic inputs are
already in the Library.

## General lemmas

- `map_le_max_of_root`: a root bound. Let `ν` be a multiplicative ring
  seminorm on `B` that extends the norm of `K`. Suppose
  `b ^ n + ∑_{j < n} a j * b ^ j = 0` and `ν (a j) ≤ C` for all `j < n`.
  Then `ν b ≤ max 1 C`. The proof is the usual ultrametric comparison: if
  `ν b > max 1 C`, the leading term is strictly larger than every other term.
- `norm_coeff_scaleRoots_le`: let `R` be a normed `K`-algebra with
  `‖1‖ ≤ 1`, let `p` be monic over `R` with all coefficient norms at most `C`,
  and let `t : K` satisfy `‖t‖ ≤ 1` and `‖t‖ * C ≤ 1`. Then every coefficient
  of `scaleRoots p t` has norm at most one.
- `norm_coeff_X_sub_C_le`: if `‖1‖ ≤ 1` and `‖a‖ ≤ 1` in a normed
  commutative ring, then every coefficient of `X - C a` has norm at most one.
- `isFiniteBanach_of_finite`: a bounded `K`-algebra map between complete
  normed commutative `K`-algebras that is module-finite is finite Banach. A
  finite generating tuple makes the Library's coefficient map surjective
  (`finite_iff_exists_surjective_coefficientMap`). The Library's open-mapping
  lemma `coefficientMap_exists_preimage_norm_le` then gives preimages with
  controlled norm, and this is the definition of `IsFiniteBanach`.

## Bounds over a target chart

- `coordinateNorm_le_of_monic`: let `q` be a monic polynomial over `A` with
  `q.eval₂ f (k-th generator of B) = 0`. Suppose every coefficient of `q`
  has norm at most `C` in the `n`-th chart algebra of `P`. Then every point
  `y` of `Spec(B)ᵃⁿ` whose image lies in the `n`-th chart of `Spec(A)ᵃⁿ`
  has `k`-th coordinate norm at most `max 1 C`. The proof applies
  `map_le_max_of_root` to the point seminorm of `y`. It uses the Library
  facts that the point seminorm of the image is the restriction of the point
  seminorm of `y`, and that chart points are bounded by the chart norm.

## The Weierstrass preimage chart

Fix chart levels `m` (for `Q`) and `n` (for `P`).

- `preimageChart P Q f m n`: the Weierstrass rational chart of the `m`-th
  chart algebra of `Q` with denominator `1`. Its numerators are the images
  of the generators of `A`, and its radii are those of the `n`-th chart of
  `P`.
- `preimageChart_locus`: its locus is the set of points `x` of the `m`-th
  chart with `x (generatorValue t) ≤ radius n` for every generator `t`.
- `preimageChart_fraction` and `preimageChart_coordinate`: the coordinates
  of the chart algebra are the images of the coordinates of the `m`-th chart
  of `Q` (first block) and of the generator values (second block).
- `preimageDomain P Q f m n`: the same chart as a local domain of the atlas
  of `Spec(B)ᵃⁿ`. Its base is transported along the Library's
  `representativeEquiv` to the selected representative of the `m`-th chart.
- `localAlgebraMap_preimageDomain` and `preimageDomain_ambientMap` identify
  its structure map from `B` and its ambient spectrum map.
- `preimageDomain_locus`: its locus is the image under `chart K Q m` of the
  set described in `preimageChart_locus`.
- `chart_image_subset_preimage`: this image lies in the preimage of the
  range of `chart K P n`.
- `chart_image_eq_preimage`: equality holds when every point over the range
  of `chart K P n` already lies in the range of `chart K Q m`.

## Finiteness

- `preimageDomain_coordinate_castAdd` and `preimageDomain_coordinate_natAdd`
  express the coordinates of the preimage domain as images of the
  generators of `B` and of the images under `f` of the generators of `A`.
- `exists_preimageDomain_lift`: there is a bounded `K`-algebra map `ψ` from
  the `n`-th chart algebra of `P` to the preimage domain algebra. It is
  compatible with `f` on the images of `A`. This is the Library's
  `exists_chart_lift`: the preimage domain maps into the preimage of the
  `n`-th chart.
- `finite_of_preimageDomain_lift`: suppose every generator of `B` satisfies
  a monic equation `q k` over `A` whose coefficients have norm at most
  `radius m` in the `n`-th chart algebra of `P`. Then every such lift `ψ` is
  module-finite. Each coordinate is divided by `scale⁻¹ ^ m` or
  `scale⁻¹ ^ n`, which have norm equal to its radius. The normalized
  coordinates of the first block satisfy the polynomials
  `scaleRoots (q k) (scale ^ m)`. The normalized coordinates of the second
  block satisfy `X - C (scale ^ n • coordinate t)`, where `coordinate t` is
  the `t`-th coordinate of the `n`-th chart algebra of `P`. Both families have
  unit-ball coefficients. `finite_of_monic_normalized_coordinates`
  (module `MonicPresentationFiniteness`) then gives finiteness.
- `exists_isFiniteBanach_preimage` (main result): assume `f.toRingHom` is
  finite and let `n : ChartIndex K P`. Then there is an index `S` of the
  saturated atlas of `Spec(B)ᵃⁿ` and an inclusion `h` with the following
  properties.
  - `h` says that the saturated morphism maps the range of chart `S` into
    the range of the saturated chart `originalSaturatedIndex n`.
  - The range of chart `S` equals the preimage of `range (chart K P n)`
    under `baseMap K P Q f`.
  - The bounded pullback `(saturatedHom K P Q f).pullback S _ h` is finite
    Banach.

### Proof of the main result

The generators of `B` are integral over `A`; let `q k` be their monic
equations. Choose `m` with `radius m` larger than the sum of the norms of all
their coefficients in the `n`-th chart algebra of `P`. By
`coordinateNorm_le_of_monic`, every point over the `n`-th chart of `P` lies
in the `m`-th chart of `Q`. So the locus of `U₀ = preimageDomain P Q f m n`
is exactly the preimage, and `S` is the saturated index with locus that of
`U₀`.

The lift `ψ` of `exists_preimageDomain_lift` is module-finite by
`finite_of_preimageDomain_lift`. It is therefore finite Banach by
`isFiniteBanach_of_finite`. The saturated representative `rS` of `S` and
`U₀` have the same locus. The restriction `ρ` from `U₀` to `rS` has a
one-sided inverse, the restriction in the other direction. So `ρ` is finite
Banach by `IsFiniteBanach.of_comp` applied to the identity. Let `γ` be the
chart lift from the `n`-th chart algebra of `P` to the saturated
representative of the original target chart. On the images of `A`, the
composite of the pullback with `γ` agrees with `ρ ∘ ψ`. This uses
`saturatedHom_pullback_localAlgebraMap` and `inclusion_localAlgebraMap`. So
the two maps are equal by `chart_hom_ext`. The composite `ρ ∘ ψ` is finite
Banach, so the pullback is finite Banach by `IsFiniteBanach.of_comp`.
