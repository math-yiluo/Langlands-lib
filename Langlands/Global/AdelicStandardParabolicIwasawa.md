# The Iwasawa integration formula for the standard parabolics of a family

Module `Langlands.Global.AdelicStandardParabolicIwasawa`.

Let `F` be a number field, `G` an affine group scheme over `Spec F`, locally of finite type, with
a compatible standard parabolic family `fam` (`StandardParabolicFamily F G`) and a standard index
`J`. Write `P = P_J`, `M = M_J`, `U = U_J` for the standard parabolic, its Levi factor and its
unipotent radical, with the closed immersions `p : P → G`, `l : M → P`, `iU : U → P`, and
`ι = map (l ≫ p) : M(𝔸) → G(𝔸)`, `ιU = map (iU ≫ p) : U(𝔸) → G(𝔸)`. Haar measures on `G(𝔸)`,
`M(𝔸)` and `U(𝔸)` are Mathlib's `Measure.haar`; on a compact subgroup `K` the measure is the
probability `compactHaarProbability F G K hK`.

## Comparison of Haar measures on a closed subgroup

`exists_integral_adelicRangeMap_eq_normalized`: for a closed immersion `j : U → G` of affine group
schemes locally of finite type such that the rational quotient of the image subgroup
(`AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range j)`) is compact, there is
`β > 0` such that `∫_{U(𝔸)} g(j(u)) du = β ∫ g dν` for every function `g` on the closed subgroup
`j(U(𝔸))`, where `du` is Mathlib's Haar measure on `U(𝔸)` and `ν` is the normalized Haar measure
`AdelicSubgroupPoints.normalizedHaarMeasure` of the closed subgroup. The image of `du` under the
homeomorphism `U(𝔸) → j(U(𝔸))` is a Haar measure, hence a positive multiple of Mathlib's Haar
measure of the subgroup, and the normalized measure is that Haar measure divided by its finite
nonzero quotient mass.

## Dynamic description and the modulus

- `definingCocharacter` uses `StandardParabolicFamily.rootPresentation` from
  `Langlands.Global.AdelicIntertwiningElementaryChainStatement` to form the split component
  cocharacter `χ_J : 𝔾_m → G`. `isRepresentedBy_parabolic`,
  `isRepresentedBy_centralizer` and `isRepresentedBy_unipotent` say that `p`, `l ≫ p` and
  `iU ≫ p` represent the dynamic parabolic `P(χ_J)`, centralizer `Z(χ_J)` and unipotent subgroup
  `U(χ_J)`.
- `leviModulus J m` (a positive real number) is the modulus `δ_P(m)` of `m ∈ M(𝔸)`: the Haar
  modulus `parabolicModulus` of conjugation by the image of `m` in `P(𝔸)` on `U(𝔸)`.
  `leviModulus_mul` (multiplicativity), `leviModulus_pos` and `continuous_leviModulus` hold.
- `leviModulus_eq_one_of_mem_normOne`: `δ_P` is trivial on the norm-one subgroup `M(𝔸)¹`. By the
  Library's `adelicParabolicModulus` the modulus is the idele norm of a rational character of `P`,
  whose restriction to `M` is a rational character of `M`, of norm one on `M(𝔸)¹`.
  `leviModulus_mul_normOne` gives `δ_P(x m) = δ_P(m)` for norm-one `x`.

## Iwasawa integration

- `exists_iwasawaIntegration`: for a compact subgroup `K` with `P(𝔸) K = G(𝔸)`
  (`IsIwasawaCompact (fam.p J) K`) there is `c > 0` such that for every compactly supported
  continuous `f` on `G(𝔸)`,
  `∫_{G(𝔸)} f = c ∫_K ∫_{M(𝔸)} ∫_{U(𝔸)} δ_P(m)⁻¹ f(ιU(u) ι(m) k) du dm dk`.
  It is the Library's `adelicIwasawaIntegration` for the cocharacter `χ_J`, the modulus there
  being identified with `leviModulus`.
- `integral_conj_normOne`: for norm-one `x ∈ M(𝔸)¹`, conjugation `u ↦ ι(x)⁻¹ ιU(u) ι(x)`
  preserves Haar measure on `U(𝔸)` (by `integral_conj_parabolicModulus` and the triviality of the
  modulus on `M(𝔸)¹`).

## Radical kernels and right convolutions

- `radicalKernel J β g k m = ∫_{U(𝔸)} β(g⁻¹ ιU(u) ι(m) k) du` for a function `β` on `G(𝔸)`,
  `g, k ∈ G(𝔸)` and `m ∈ M(𝔸)`.
- `exists_rightConvolution_eq_iwasawa`: with `c` as above, for every compactly supported
  continuous `β`, every continuous `φ` on `G(𝔸)` left invariant under `ιU(U(𝔸))`, every norm-one
  `x` and every `g`,
  `(β * φ)(ι(x) g) = c ∫_K ∫_{M(𝔸)} δ_P(m)⁻¹ radicalKernel J β g k (x⁻¹ m) φ(ι(m) k) dm dk`,
  where `β * φ = rightConvolution F G β φ`, `(β * φ)(y) = ∫ β(s) φ(y s) ds`. The proof applies
  the Iwasawa formula to `z ↦ β((ι(x) g)⁻¹ z) φ(z)`, uses the `U(𝔸)`-invariance of `φ`, and
  substitutes `u ↦ ι(x)⁻¹ u ι(x)` by `integral_conj_normOne`.
- `leviProjection : P(𝔸) → M(𝔸)` is the continuous homomorphism induced by the Levi retraction
  `P → M` (module `Langlands.GroupScheme.Rational.LeviRetraction`); it kills `U(𝔸)`
  (`leviProjection_radical`) and is the identity on `M(𝔸)` (`leviProjection_levi`).
- `exists_compact_radicalKernel_support`: for compactly supported continuous `β` and compact sets
  of `g` and of `k`, the radical kernels vanish outside one compact subset of `M(𝔸)`. If the
  kernel at `m` is nonzero, some `ιU(u) ι(m) = g s k⁻¹` with `s` in the support of `β`; this
  point of `P(𝔸)` lies in the compact preimage under the closed embedding `P(𝔸) → G(𝔸)` of a
  compact set, and `m` is its Levi projection.
- `exists_compact_radicalKernel_integrand_support`: for `g`, `k`, `m` in compact sets, the
  integrand `u ↦ β(g⁻¹ ιU(u) ι(m) k)` vanishes outside one compact subset of `U(𝔸)` (the
  preimage under the closed embedding `ιU` of a compact set).
- `continuous_radicalKernel`: the radical kernel of a compactly supported continuous `β` is
  jointly continuous in `(g, k, m)`. Locally the integral runs over a fixed compact set, and a
  parametric integral of a continuous function over a compact set is continuous.

## Provenance

This is an internal development of the Library's Iwasawa integration theorem
(`adelicIwasawaIntegration`, module `Langlands.Global.AdelicIwasawaIntegrationProof`) and its
modulus (`adelicParabolicModulus`, module `Langlands.Global.AdelicParabolicModulusProof`) for the
standard parabolics of a family. It serves the Iwasawa unfolding of the norm-one Levi pairings of
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series* (2024), §6.2, (6.8),
p. 202, carried out in `Langlands.Global.AdelicLeviPairingIwasawa`.
