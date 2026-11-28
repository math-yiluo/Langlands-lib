# Iwasawa unfolding of the norm-one Levi pairing of a right convolution

Module `Langlands.Global.AdelicLeviPairingIwasawa`.

Notation as in `Langlands.Global.AdelicStandardParabolicIwasawa`: a number field `F`, an affine
group scheme `G` over `Spec F`, locally of finite type, a compatible standard parabolic family
`fam` with standard index `J`, Levi factor `M = M_J`, radical `U = U_J`,
`ι : M(𝔸) → G(𝔸)`, `ιU : U(𝔸) → G(𝔸)`, the modulus `δ = leviModulus J` and the radical kernel
`K_{g,k}(m) = radicalKernel J β g k m = ∫_{U(𝔸)} β(g⁻¹ ιU(u) ι(m) k) du`. Write
`M(𝔸)¹ = normOneSubgroup F M`, `X₁ = NormOneRationalQuotient F M = M(F) \ M(𝔸)¹` with the measure
`normOneRationalQuotientHaarMeasure F M`, and `x_ξ = Quotient.out ξ` for the representative of
`ξ ∈ X₁`. The norm-one Levi pairing is the Library's
`leviPairing J f g t = ∫_{X₁} f(ι(x_ξ) g) conj t(x_ξ) dξ`.

## A triple Fubini rearrangement

`integral_integral_integral_comm`: for s-finite measures and `f(a, b, c)` integrable on the
product `μ × (ν × ρ)`, `∫_a ∫_b ∫_c f = ∫_b ∫_c ∫_a f` (Fubini on the pair `(b, c)`, an exchange
of `a` with the pair, and Fubini again).

## The integrand

`iwasawaPairingIntegrand J β φ t g k x z = δ(z)⁻¹ K_{g,k}(z) φ(ι(x z) k) conj t(x)` for functions
`β`, `φ` on `G(𝔸)`, `t` on `M(𝔸)`, `g, k ∈ G(𝔸)` and `x, z ∈ M(𝔸)`. For a compact subgroup `K`
of `G(𝔸)` and compactly supported continuous `β`:

- `continuous_iwasawaPairingIntegrand`: if `φ` is continuous and left invariant under `ι(M(F))`,
  and `t` is continuous on `M(𝔸)¹` and left invariant under `M(F)`, the integrand at
  `(x_ξ, k, z)` is continuous on `X₁ × (K × M(𝔸))` (by `continuous_out_prod'`; the integrand is
  invariant under `x ↦ r x` for rational `r`).
- `exists_iwasawaPairingIntegrand_bound`: there are a compact `C ⊆ M(𝔸)` and `B ≥ 0` with
  `|integrand(k, x, z)| ≤ 1_C(z) B |φ(ι(x z) k)| |t(x)|` for all `k ∈ K`; `C` contains the
  supports of the kernels `K_{g,k}`, `k ∈ K` (`exists_compact_radicalKernel_support`), and `B`
  bounds `δ(z)⁻¹ |K_{g,k}(z)|` on the compact `K × C`.
- The domination hypothesis used below: for every compact `C ⊆ M(𝔸)` there is an integrable `W`
  on `X₁` such that for almost every `ξ`, every `k ∈ K` and every `z ∈ C`,
  `|φ(ι(x_ξ z) k)| |t(x_ξ)| ≤ W(ξ)`.
- `integrable_iwasawaPairingIntegrand`: under this hypothesis the integrand is integrable on
  `X₁ × (K × M(𝔸))` for `dξ × (dk × dz)`, dominated by `W(ξ) B 1_C(z)`.
- `leviPairing_eq_integral_iwasawaPairingIntegrand`: if `(β * φ)(ι(x) g)` is given for norm-one
  `x` by the formula of `exists_rightConvolution_eq_iwasawa` with constant `c`, then
  `leviPairing J (β * φ) g t = c ∫_{X₁} ∫_K ∫_{M(𝔸)} integrand(k, x_ξ, z) dz dk dξ`. The
  Levi variable is substituted as `m = x_ξ z`, and `δ(x_ξ z) = δ(z)`.

## Positive and norm-one coordinates

Under split central data for `M` — a split torus `T` with `e : T ≅ 𝔾_m^I`, a central `i : T → M`
whose restriction of rational characters `characterRestrict i` is injective with finite-index
image — `M(𝔸)` is the direct product of the positive points `b ∈ T⁺` (through
`positivePointMap`) and `M(𝔸)¹`, and Haar measure of `M(𝔸)` is the product of
`normalizedPositiveHaarMeasure` and Haar measure of `M(𝔸)¹`
(`measurePreserving_normOneDecomposition`).

- `integral_eq_integral_positive_normOne`: `∫_{M(𝔸)} f = ∫_{T⁺} ∫_{M(𝔸)¹} f(b n) dn db` for
  integrable `f`.
- `integrable_iwasawaPairingIntegrand_normOne`: for fixed `k ∈ K` and `b ∈ T⁺`, under the
  domination hypothesis, `(ξ, n) ↦ integrand(k, x_ξ, b n)` is integrable on `X₁ × M(𝔸)¹`; if
  `b n ∈ C` then `n` lies in the compact image of `C` under the norm-one factor map.
- `integral_iwasawaPairingIntegrand_normOne_eq`: for fixed `k` and `b`,
  `∫_{X₁} ∫_{M(𝔸)¹} integrand(k, x_ξ, b n) dn dξ =
  δ(b)⁻¹ ∫_{X₁} φ(ι(b x_ξ) k) ∫_{M(𝔸)¹} K_{g,k}(b x⁻¹ x_ξ) conj t(x) dx dξ`.
  Here `δ(b n) = δ(b)`, `b` is central, the inner variable is substituted as `y = x_ξ n`, and the
  diagonal exchange `integral_integral_swap_diagonal` (module
  `Langlands.Global.LeftCosetDiagonalSwap`) is applied on `M(𝔸)¹` with `Γ = M(F)` to
  `Φ(x, y) = K_{g,k}(b x⁻¹ y) φ(ι(b y) k) conj t(x)`. Its hypotheses: Haar measure of `M(𝔸)¹` is
  right invariant (`normOneHaarRightInvariant`), and `Φ` is invariant under the diagonal action of
  `M(F)` because `φ` and `t` are left invariant under rational points and `b` is central.

## The unfolding theorem

`leviPairing_rightConvolution_eq_iwasawa`: let `K` be a compact subgroup with
`P_J(𝔸) K = G(𝔸)` (`IsIwasawaCompact (fam.p J) K`). There is `c > 0` such that for every compactly
supported continuous `β`, every continuous `φ` on `G(𝔸)` left invariant under `ιU(U(𝔸))` and
under `ι(M(F))`, every function `t` on `M(𝔸)`, continuous on `M(𝔸)¹` and left invariant under
`M(F)`, and every `g ∈ G(𝔸)` satisfying the domination hypothesis,

`leviPairing J (β * φ) g t = c ∫_K ∫_{T⁺} δ(b)⁻¹ ∫_{X₁} φ(ι(b x_ξ) k)
  ∫_{M(𝔸)¹} K_{g,k}(b x⁻¹ x_ξ) conj t(x) dx dξ db dk`.

The inner integral over `M(𝔸)¹` is the complex conjugate of the norm-one partial convolution of
`t` against the kernel `w ↦ K_{g,k}(b w)`. The constant `c` is that of
`exists_rightConvolution_eq_iwasawa`. The proof combines
`leviPairing_eq_integral_iwasawaPairingIntegrand`, the triple rearrangement (moving `X₁`
innermost), the positive and norm-one coordinates for almost every `k`, Fubini for each `(k, b)`
and `integral_iwasawaPairingIntegrand_normOne_eq`. The function `t` need not be a cusp form; only
continuity, rational invariance and the domination hypothesis are used.

## Provenance

This is an internal computation: the Iwasawa decomposition of the norm-one Levi pairings
`(φ(· g), t)_{X_M¹}` of Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*
(2024), §6.2, (6.8), p. 202, applied to a right convolution `β * φ`, which expresses the pairing
through the fibres of `φ` over `M(F) \ M(𝔸)¹` and norm-one partial convolutions of `t`.
