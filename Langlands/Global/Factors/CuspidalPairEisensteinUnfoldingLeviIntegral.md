# The Levi integral is the Levi Whittaker coefficient

Module `Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingLeviIntegral` (namespace
`Langlands.Global.CuspidalPairEisenstein.Unfolding`) evaluates the inner integral of the open
cell. Let `f` be a continuous function on `GL_N(𝔸)` that is left invariant under `P(F)`, let
`ψ` be a standard additive character of `𝔸` (`IsStandardAdditiveCharacter F ψ`), and let
`g ∈ GL_N(𝔸)`. Assume that the function

```text
f(leviPair B A · g) · conj(ψ_(t+1)(A)) · conj(ψ_(r+1)(B)),    (A, B) ∈ N_(t+1)(𝔸) × N_(r+1)(𝔸),
```

is integrable on the fundamental domain `fdM` of `N_(t+1)(F) × N_(r+1)(F)` for the normalized
measure `haarM`. Then its integral over `fdM` is `leviWhittaker F r t ψ f g`. The triviality of
`ψ` on `F` makes the function invariant under `N_(t+1)(F) × N_(r+1)(F)`, which lets the
integral move to a product fundamental domain. Here `leviWhittaker` is the iterated Library
global Whittaker coefficient of
[CuspidalPairEisensteinOpenCell.md](CuspidalPairEisensteinOpenCell.md).

This is the two-block `GL_N` analogue of the Levi integral in Shahidi, *Functional equation
satisfied by certain L-functions*, Compositio Math. 37 (1978), Lemma 2.1 and its proof,
pp. 181–182. The open-cell formula (2.10) of Lemma 2.1, p. 181, integrates over
`u' ∈ N_𝔸` inside and over the Levi quotient `°U_𝔸 / °U_F` outside. The order used here, with
the Levi quotient inside, is that of the single term of (2.10.3) in the paragraph after
(2.10.3), p. 182: there the integral over `V_𝔸 / V_F`, `V = wPw⁻¹ ∩ U`, is inside the integral
over `N^V_𝔸`. For the open class the two-block `GL_N` counterpart of `V` is the upper
unitriangular group `N_(t+1) × N_(r+1)` of a Levi subgroup
([CuspidalPairEisensteinUnfoldingOpenGroups.md](CuspidalPairEisensteinUnfoldingOpenGroups.md)).
Shahidi, *On certain L-functions*, Amer. J. Math. 103 (1981), proof of Theorem 5.1,
p. 351, applies Lemma 2.1 of the 1978 paper to factor the Fourier coefficient into local
Whittaker functions.

## Normalization

- `latticeNormalizedHaar_eq`: for a discrete subgroup `Γ`, a Haar measure `μ` and a measurable
  strict fundamental domain `S`, the Library's `LeftCosetSpace.Semidirect.latticeNormalizedHaar`
  equals `μ(S)⁻¹ • μ`. The quantity `μ(S)⁻¹ • μ` depends neither on the Haar measure nor on the
  fundamental domain.
- `fdProd = fd₀(t + 1) ×ˢ fd₀(r + 1)` is a measurable strict fundamental domain of
  `N_(t+1)(F) × N_(r+1)(F)` (`measurableSet_fdProd`, `existsUnique_mem_fdProd`).
  `haarM_eq_prod`: `haarM` is the product Haar measure divided by the mass of `fdProd`.
- `haar_fd₀_ne_zero`, and `unipotentNormalizer_eq`: the Library's mass normalizer of
  `N_n(F) \ N_n(𝔸)` is `(haar fd₀(n))⁻¹` (from
  `RankinSelbergGlobal.Unfolding.haar_unipotentFundamentalDomain`).

## The integrand

- `continuous_leviPair`, `twisted_leviPair_rational_left`:
  `f(leviPair (a x) (b y) · g) = f(leviPair x y · g)` for rational `a`, `b`, by
  `leviPair_rational`. `toMat_mem_rational_of_mem_Γ₀`: the matrix of a point of `N_n(F)` is
  rational.
- `leviIntegrand f ψ g m`, the integrand above with `m = (A, B)`. `leviIntegrand_mul`: it is
  left invariant under `N_(t+1)(F) × N_(r+1)(F)`.

## Whittaker coefficients as set integrals

- `genericCharacter_mul_rational`: the Library's generic character is left invariant under
  `N_(n+1)(F)` when `ψ` is trivial on `F`.
- `innerWhittaker_eq` and `leviWhittaker_eq`: by the Library's
  `RankinSelbergGlobal.Unfolding.subgroupCharacterCoefficient_eq_setIntegral`, applied twice,

  ```text
  leviWhittaker f g = c_(r+1) ∫_{B ∈ fd₀(r+1)} (c_(t+1) ∫_{A ∈ fd₀(t+1)}
      f(leviPair B A · g) conj(ψ_(t+1)(A)) dA) conj(ψ_(r+1)(B)) dB
  ```

  for Haar measures, with `c_n = unipotentNormalizer F n`. Measurability of the inner integral
  in `B` comes from Mathlib's `StronglyMeasurable.integral_prod_right'`.
- `setIntegral_fdM_eq_leviWhittaker` (**the Levi integral**): if `leviIntegrand f ψ g` is
  integrable on `fdM` for `haarM`, then
  `∫_{fdM} leviIntegrand f ψ g dhaarM = leviWhittaker F r t ψ f g`. The integral over `fdM`
  equals the integral over `fdProd` (Mathlib's `IsFundamentalDomain.setIntegral_eq`, using
  `leviIntegrand_mul`). By `haarM_eq_prod` and Fubini (`integral_prod_symm`), it becomes the
  iterated integral above. The constants agree because
  `(haar fd₀(t+1) · haar fd₀(r+1))⁻¹ = c_(r+1) c_(t+1)`.
