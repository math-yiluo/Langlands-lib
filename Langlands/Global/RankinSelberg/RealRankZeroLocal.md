# The rank-one real local Rankin–Selberg functional equation from Tate's theory

Helper module for the rank-one (`r = 0`) case of
`Langlands.Global.RankinSelbergGlobal.RealEqualFunctionalEquationStatement`.
Every declaration is proved. The main theorem `realEqual_rankZero` assumes the
Library proposition `Langlands.LocalFactor.RealArchimedeanTateStatement` as a hypothesis
`hTate`; nothing else is assumed and no axioms are added.

All declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal.RealRankZero`. The module imports
`RealRankZeroHaar` (the quotient measure on `N₁(ℝ) \ GL₁(ℝ)`) and `RealTateZeta` (the real
Tate zeta integral `RealTate.zeta f e u = ∫ f(x) sgn(x)^e |x|^(u-1) dx`, which is
holomorphic in `Re u > 0`).

## Notation

`c, c'` are `RealCharacterData`: a parity `e ∈ Fin 2` and an exponent `t ∈ ℂ`, giving the
character `χ(x) = sgn(x)^e |x|^t` of `ℝˣ`. Their product `c.mul c'` has parity `p` and
exponent `t` (the sum of the parities mod 2 and the sum of the exponents). In this module,
`W = C · χ_c ∘ det` and `W' = C' · χ_{c'} ∘ det` on `GL₁(ℝ)`, for constants `C, C' ∈ ℂ`.
The additive character is `ψ_a(x) = exp(2π i a x)` with `a ∈ ℝˣ`.

## The line restriction and the Fourier transform

- `lineSchwartz Φ : 𝓢(ℝ, ℂ)` is `x ↦ Φ(x)` for a Schwartz function `Φ` on `ℝ¹`
  (composition with the continuous linear equivalence `ℝ ≃ (Fin 1 → ℝ)`);
  `lineSchwartz_apply` is its evaluation.
- `tateFourier a c f y = c ∫ exp(2π i a x y) f(x) dx`. This is the Fourier transform
  `ft a c f` that appears inside `RealArchimedeanTateStatement`.
- `realFourierTransform_const`: the Library's `realFourierTransform a Φ`, evaluated at the
  constant vector `(y)`, equals `tateFourier a (√|a|) (lineSchwartz Φ) y`. The self-dual
  measure for `ψ_a` is `√|a|` times Lebesgue measure, and the measure-preserving map
  `ℝ → (Fin 1 → ℝ)` carries the integral over `ℝ¹` to an integral over `ℝ`.

## Evaluation at scalar matrices

The class of `u ∈ ℝˣ` in `N₁ \ GL₁` has the scalar matrix `tateScalarEquiv ℝ u` as its
representative. The following are its evaluations:
`determinant_tateScalarEquiv`, `det_val_tateScalarEquiv` (the determinant is `u`),
`lastRow_tateScalarEquiv` (the last row is `(u)`), `detPower_tateScalarEquiv`
(`|det|^s = |u|^s`). `dualFunction_apply` shows that in rank one
`W̃(g) = W(ᵗg⁻¹)`, because the long Weyl element of `GL₁` is `1`.

## Sign and absolute-value algebra

- `sgn x = x / |x|`, as a complex number.
- `character_mul_character`: `χ_c(u) χ_{c'}(u) = sgn(u)^p |u|^t`.
- `character_inv_mul_character_inv`: `χ_c(u)⁻¹ χ_{c'}(u)⁻¹ = sgn(u)^p |u|^(-t)`, because
  `sgn(u)^p · sgn(u)^p = 1`.
- `character_inv_apply`: `χ(u⁻¹) = χ(u)⁻¹`.
- `abs_cpow_shift`: `|x|⁻¹ |x|^t |x|^s = |x|^(s+t-1)` for `x ≠ 0`.

## The integrands on the line

The section `Integrands` assumes `hW : ∀ g, W g = C · χ_c(det g)` and the matching
`hW'` for `W'`.

- `extend_equalIntegrand`: for every `x ∈ ℝ`,
  `|x|⁻¹ · (unitsExtend (realEqualIntegrand W W' Φ s))(x)
  = C C' · RealTate.integrand (lineSchwartz Φ) p (s + t) x`.
  At `x ≠ 0` this is the evaluation of `W(g) W'(g) Φ(e_n g) |det g|^s` at the scalar
  matrix `g = x`, followed by the algebra above. At `x = 0` both sides are `0`.
- `extend_dualIntegrand`: the same for the dual integrand
  `W̃(g) W̃'(g) Φ̂(e_n g) |det g|^s`:
  `|x|⁻¹ · (unitsExtend …)(x) = C C' · RealTate.integrand (tateFourier a √|a| (lineSchwartz Φ)) p (s - t) x`.
  It uses `dualFunction_apply`, `det(ᵗg⁻¹) = (det g)⁻¹` and `realFourierTransform_const`.
- `equalIntegral_eq`: if `D.measure = κ • (quotientUnits.symm)_* unitsHaar`, then for
  every `s ∈ ℂ`,
  `realEqualIntegral D W W' Φ s = κ · (C C' · RealTate.zeta (lineSchwartz Φ) p (s + t))`.
  The proof uses `integral_eq` from `RealRankZeroHaar` and the pointwise identity above.
- `equalDualIntegral_eq`: under the same hypothesis,
  `realEqualDualIntegral a D W W' Φ s = κ · (C C' · RealTate.zeta (tateFourier a √|a| (lineSchwartz Φ)) p (s - t))`
  for every `s`.
- `integrable_equalIntegrand`: if additionally `κ ≠ 0` and `0 < Re(s + t)`, the integrand
  of `Ψ(s; W, W', Φ)` is `D.measure`-integrable. The proof uses `integrable_iff` and the
  integrability of the real Tate integrand of a Schwartz function in `Re u > 0`
  (`RealTate.integrable_integrand`).
- `integrable_dualIntegrand`: the same for the dual integrand when `0 < Re(s - t)`. Here
  the Fourier transform is given as a Schwartz function `g` with
  `⇑g = tateFourier a √|a| (lineSchwartz Φ)`.

## Rank-one factors

- `realPairBlocks_character`: the pair of the single character blocks `[c]` and `[c']` is
  the single block `[c.mul c']` (by definition).
- `realPairLFactor_character`: the denominator of
  `realPairLFactor [character c] [character c']` at `s` is `Γℝ(s + (t + p))⁻¹`.
- `realPairEpsilon_character`: for `c₀ > 0`,
  `realPairEpsilon [character c] [character c'] a c₀ s = c₀ sgn(a)^p |a|^(s+t-1) i^p`.
  The proof starts from the Library's `RealCharacterData.coe_epsilon`
  (`c₀ χ(a) |a|^(s-1) i^p`) and uses `|a|^t |a|^(s-1) = |a|^(s+t-1)`.
- `reflectedGamma t q`: the entire function `s ↦ Γℝ(1 - s - t + q)⁻¹`, as a
  `ReciprocalEntire`. It is used only to name the discrete set of poles of
  `Γℝ(1 - s - t + q)`.

## The main theorem

`realEqual_rankZero` assumes `hTate : RealArchimedeanTateStatement`, `a ∈ ℝˣ`, character
data `c, c', cd, cd'` with `(cd.mul cd').parity = (c.mul c').parity` and
`(cd.mul cd').exponent = -(c.mul c').exponent`, `D : RealQuotientMeasureData 0`, `hW`,
`hW'` as above and a Schwartz function `Φ` on `ℝ¹`. Its conclusion is the conclusion of
`RealEqualFunctionalEquationStatement` at `r = 0`, with parameters
`d = [character c]`, `d' = [character c']`, `dd = [character cd]`,
`dd' = [character cd']`, and with the factor `realMinusOneScalar T' v ^ 0` omitted
(it equals `1`). That is, there are `σ ∈ ℝ` and `M, Md : ℂ → ℂ` such that:

1. both integrands are `D.measure`-integrable for `Re s > σ`;
2. `s ↦ Ψ(s; W, W', Φ)` and `s ↦ Ψ(s; W̃, W̃', Φ̂)` are holomorphic on `Re s > σ`;
3. `M` and `Md` are meromorphic on `ℂ` and agree with the two integrals on `Re s > σ`;
4. for `s` outside a discrete subset of `ℂ` (the filter `codiscrete ℂ`),
   `L(s, d × d')⁻¹ · Md(1 - s) = ε(s, d × d', ψ_a) · L(1 - s, dd × dd')⁻¹ · M(s)`.

The proof follows these steps.

- `exists_measure_eq` (from `RealRankZeroHaar`) gives `κ ≠ 0` with
  `D.measure = κ • (quotientUnits.symm)_* unitsHaar`.
- From `hTate`, the continuation part gives a meromorphic `Z` with
  `Z(s) = RealTate.zeta (lineSchwartz Φ) p (s + t)` for `Re(s + t) > 0`. The
  functional-equation part, applied with `c = √|a|`, gives a Schwartz function `g` equal to
  `tateFourier a √|a| (lineSchwartz Φ)` together with the local functional equation for
  `Z` and any continuation `Y` of the zeta integral of `g` with exponent `-t`. The
  continuation part gives such a `Y`.
- Set `σ = |Re t|`, `M(s) = κ C C' Z(s)` and `Md(s) = κ C C' Y(s)`. Then `Re s > σ`
  implies `Re(s + t) > 0` and `Re(s - t) > 0`.
- Integrability follows from `integrable_equalIntegrand` and `integrable_dualIntegrand`.
- Holomorphy: `equalIntegral_eq` and `equalDualIntegral_eq` write both integrals as
  constant multiples of `s ↦ RealTate.zeta _ p (s ± t)`. These are holomorphic at every
  point with `Re(s ± t) > 0` (`RealTate.differentiableAt_zeta`).
- Meromorphy: `Z` and `Y` are meromorphic in normal form, so they are meromorphic; a
  constant times a meromorphic function is meromorphic.
- Agreement: on `Re s > σ`, `equalIntegral_eq` and the continuation property of `Z` give
  the first agreement, and likewise for `Y`.
- Functional equation: by `eventually_codiscrete_iff_forall_eventually_nhdsNE` it suffices
  to prove it in a punctured neighbourhood of every `s₀`. There, the following hold
  simultaneously: Tate's functional equation
  `Y(1-s) / Γℝ(1-s-t+p) = √|a| sgn(a)^p |a|^(s+t-1) i^p · Z(s) / Γℝ(s+t+p)`,
  `Γℝ(s+t+p) ≠ 0` and `Γℝ(1-s-t+p) ≠ 0`. The nonvanishing comes from the Library's
  `ReciprocalEntire.denominator_eventually_ne_zero` for `gammaReal.shift (t + p)` and
  `reflectedGamma t p`. By `realPairLFactor_character` and the hypotheses on `cd, cd'`,
  `L(s, d × d')⁻¹ = Γℝ(s + t + p)` and `L(1 - s, dd × dd')⁻¹ = Γℝ(1 - s - t + p)`.
  `realPairEpsilon_character` identifies ε with the factor in Tate's equation. Clearing
  denominators (`field_simp`) gives the claim.

## Provenance

The functional equation of the rank-one Rankin–Selberg integral is Tate's local
functional equation at the real place (Tate's thesis; Cassels–Fröhlich 1967, Chapter XV),
stated in the Library as `RealArchimedeanTateStatement`. It is the case `n = 1` of
Jacquet, *Archimedean Rankin–Selberg integrals* (2009), Theorem 2.1. The reduction of the
`GL₁ × GL₁` integrals to Tate integrals of the line restriction of `Φ` and of its Fourier
transform is internal to this project.
