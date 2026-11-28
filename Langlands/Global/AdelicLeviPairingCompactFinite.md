# Iwasawa unfolding of Levi pairings for right `K`-finite functions

Module `Langlands.Global.AdelicLeviPairingCompactFinite`.

Notation as in `Langlands.Global.AdelicLeviPairingIwasawa`: a compatible standard parabolic family
`fam` of `G` over a number field `F`, a standard index `J` with Levi factor `M = M_J` and radical
`U = U_J`, the modulus `δ = leviModulus J`, the radical kernels
`radicalKernel J β g k m = ∫_{U(𝔸)} β(g⁻¹ ιU(u) ι(m) k) du`, the norm-one quotient
`X₁ = M(F) \ M(𝔸)¹` with representatives `x_ξ`, and the Library's `leviPairing`.

## Averaged kernels

- `compactRightAverageCc K hK a ha β` is the compactly supported continuous function
  `z ↦ ∫_K a(k) β(z k) dk` (`maximalCompactRightAverage`, module
  `Langlands.Global.AdelicTestFunctionCompactAverage`), for a compact subgroup `K` of `G(𝔸)`, a
  continuous weight `a` and a compactly supported continuous `β`. Continuity is that of a
  parametric integral over the compact group. The support lies in `supp β · K⁻¹`.
- `integral_mul_radicalKernel`: `∫_K a(k) radicalKernel J β g k w dk` is the radical kernel of the
  average at `(g, 1)`: `radicalKernel J (compactRightAverageCc K hK a ha β) g 1 w` (Fubini on
  `K × U(𝔸)`; the integrand is continuous with compact support by
  `exists_compact_radicalKernel_integrand_support`).

## Right convolutions

`rightConvolution_eq_iwasawa_finite`: let `K` satisfy `P_J(𝔸) K = G(𝔸)`, and let `c` and the
formula `hconv` be those of `exists_rightConvolution_eq_iwasawa`. If `φ` is continuous, left
invariant under `ιU(U(𝔸))`, and `φ(z k) = ∑_j a_j(k) φ(z k_j)` for `k ∈ K`, with continuous
weights `a_j` and points `k_j ∈ K`, then for norm-one `x` and `g ∈ G(𝔸)`,

`(β * φ)(ι(x) g) = c ∑_j ∫_{M(𝔸)} δ(m)⁻¹ K_j(x⁻¹ m) φ(ι(m) k_j) dm`,

where `K_j = radicalKernel J (compactRightAverageCc K hK (a_j) ha_j β) g 1`. The compact integral of
`exists_rightConvolution_eq_iwasawa` is distributed over the finite sum, exchanged with the
`M(𝔸)`-integral (Fubini on `K × M(𝔸)`; the integrand is continuous and vanishes outside
`K × x C` for the compact support set `C` of `exists_compact_radicalKernel_support`), and
absorbed into the kernel by `integral_mul_radicalKernel`.

## Pairings

- `integrable_iwasawaPairingIntegrand_fixed`: for a fixed point `k` of `K`, the Iwasawa
  integrand `iwasawaPairingIntegrand` at `(x_ξ, k, z)` is integrable on `X₁ × M(𝔸)` under the
  domination hypothesis of `Langlands.Global.AdelicLeviPairingIwasawa`.
- `integral_iwasawaPairingIntegrand_fixed_eq`: under split central data for `M` (positive points
  `b` through `positivePointMap`, `νP = normalizedPositiveHaarMeasure`), for a fixed `k`,
  `∫_{X₁} ∫_{M(𝔸)} integrand(k, x_ξ, z) dz dξ =
  ∫_{T⁺} δ(b)⁻¹ ∫_{X₁} φ(ι(b x_ξ) k) ∫_{M(𝔸)¹} radicalKernel J β g k (b x⁻¹ x_ξ) conj t(x) dx dξ db`,
  by Fubini, `integral_eq_integral_positive_normOne`,
  `integrable_iwasawaPairingIntegrand_normOne` and `integral_iwasawaPairingIntegrand_normOne_eq`.
- `leviPairing_rightConvolution_eq_iwasawa_finite`: there is `c > 0` such that, with `φ` as in the
  convolution formula, moreover left invariant under `ι(M(F))`, `t` continuous on `M(𝔸)¹` and
  left invariant under `M(F)`, and the domination hypothesis at `g`,

  `leviPairing J (β * φ) g t = c ∑_j ∫_{T⁺} δ(b)⁻¹ ∫_{X₁} φ(ι(b x_ξ) k_j)
    ∫_{M(𝔸)¹} K_j(b x⁻¹ x_ξ) conj t(x) dx dξ db`,

  with `K_j` the radical kernels at `(g, 1)` of the averages of `β` with weights `a_j`. The proof
  applies the convolution formula at each representative, substitutes `m = x_ξ z`, separates the
  finite sum (each term is integrable by `integrable_iwasawaPairingIntegrand_fixed`), and applies
  `integral_iwasawaPairingIntegrand_fixed_eq` to the right translate `w ↦ φ(w k_j)` at the point
  `k = 1` of `K`.

## Provenance

This is an internal computation: the Iwasawa decomposition of the norm-one Levi pairings of
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series* (2024), §6.2, (6.8),
p. 202, in a form in which only finitely many kernels on the Levi factor occur.
