# The rank-one complex local Rankin–Selberg functional equation from Tate's theory

Helper module for the rank-one (`r = 0`) case of the complex equal-rank local premise
`Langlands.Global.RankinSelbergGlobal.ComplexLocalEqualFunctionalEquationStatement`.
It is the complex analogue of
`Langlands.Global.RankinSelberg.RealRankZeroLocal`. Every declaration is proved. The main
theorem `complexEqual_rankZero` assumes the Library proposition
`Langlands.LocalFactor.ComplexArchimedeanTateStatement` (complex Tate theory, which the Library
proves in `Langlands.LocalFactor.Archimedean.ComplexTateProof`) as a hypothesis `hTate`. Nothing else is assumed and no axioms are added.

All declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal.ComplexRankZero`. The module imports
`ComplexRankZeroHaar`, which provides the quotient measure on `N₁(ℂ) \ GL₁(ℂ)`.

## Notation

`c, c'` are `ComplexCharacterData`: an integer weight `m` and an exponent `t ∈ ℂ`, giving
the character `χ(z) = (z/|z|)^m |z|^(2t)` of `ℂˣ` (`ComplexCharacterData.character_eq`).
Their product `c.mul c'` has weight `m = m_c + m_{c'}` and exponent `t = t_c + t_{c'}`.
`W = C · χ_c ∘ det` and `W' = C' · χ_{c'} ∘ det` on `GL₁(ℂ)`, for constants `C, C' ∈ ℂ`.
The additive character is `ψ_a(z) = exp(2π i Tr(a z)) = exp(4π i Re(a z))` with `a ∈ ℂˣ`.
The normalized absolute value on `ℂ` is `|z|_ℂ = |z|²`.

## Complex Tate zeta integrals (`ComplexTate`)

The definitions in this namespace copy the local `let` definitions inside
`ComplexArchimedeanTateStatement`, and are definitionally equal to them. The measure is
`2 ·` Lebesgue measure on `ℂ`, as in that statement.

- `integrand f m t s z = f(z) (z/|z|)^m |z|^(2(s+t)-2)` for `z ≠ 0`, and `0` at `z = 0`.
- `zeta f m t s = ∫ integrand f m t s z d(2·Lebesgue)(z)`.
- `ExtendsIntegral Z f m t`: `Z` is meromorphic in normal form on `ℂ` and equals
  `zeta f m t s` whenever `Re(s + t) > 0`.
- `tateFourier a c f y = c ∫ exp(4π i Re(a z y)) f(z) d(2·Lebesgue)(z)`.
- `integral_two_smul`: an integral for `2 ·` Lebesgue is twice the Lebesgue integral.
- `norm_integrand`: for `z ≠ 0`, `|integrand f m t s z| = |f(z)| |z|^(2 Re(s+t) - 2)`.
- `rpow_le_add`: for `x > 0` and `a ≤ y ≤ b`, `x^y ≤ x^a + x^b`.
- `norm_integrand_le`: on the strip `a ≤ Re(s + t) ≤ b`, the integrand at `s` is bounded by
  the sum of the norms of the integrands at the points with `s + t = a` and `s + t = b`.
- `continuousAt_integrand`: for fixed `z`, the integrand is continuous in `s`.
- `continuousAt_zeta`: if the integrand is integrable for every `s` with `Re(s + t) > 0`
  (hypothesis `hint`), then `zeta f m t` is continuous at every `s₀` with
  `Re(s₀ + t) > 0`. The proof is dominated convergence
  (`continuousAt_of_dominated`) on the strip `Re(s₀+t)/2 < Re(s + t) < Re(s₀+t) + 1`, with
  the bound of `norm_integrand_le`.
- `differentiableAt_zeta`: under `hint` and `ExtendsIntegral Z f m t`, `zeta f m t` is
  complex differentiable at every `s₀` with `Re(s₀ + t) > 0`. Near `s₀`, `Z` agrees with
  `zeta f m t` on an open half-plane, so `Z` is continuous at `s₀`. A meromorphic function
  that is continuous at a point is analytic there (Mathlib's `MeromorphicAt.analyticAt`).
  Hence `zeta f m t` is differentiable at `s₀`.

So holomorphy of the complex Tate zeta integral is derived from the continuation part of
`ComplexArchimedeanTateStatement` and integrability, not proved by differentiating under
the integral.

## The line restriction and the Fourier transform

- `lineSchwartz Φ : 𝓢(ℂ, ℂ)` is `z ↦ Φ(z)` for a Schwartz function `Φ` on `ℂ¹`. It is the
  composition with the continuous linear equivalence `ℂ ≃ (Fin 1 → ℂ)`. `lineSchwartz_apply`
  is its evaluation.
- `complexFourierTransform_const`: the Library's `complexFourierTransform a Φ`, evaluated
  at the constant vector `(y)`, equals `tateFourier a |a| (lineSchwartz Φ) y`. The
  self-dual measure for `ψ_a` is `|a| · (2·Lebesgue)` (`complexSelfDualMeasure`). The
  measure-preserving map `ℂ → (Fin 1 → ℂ)` carries the integral over `ℂ¹` to an integral
  over `ℂ`. The character value is `exp(2π i Tr(a z y)) = exp(4π i Re(a z y))`.

## Evaluation at scalar matrices

The class of `u ∈ ℂˣ` in `N₁ \ GL₁` has the scalar matrix `tateScalarEquiv ℂ u` as its
representative. Its evaluations are `determinant_tateScalarEquiv` and
`det_val_tateScalarEquiv` (the determinant is `u`), `lastRow_tateScalarEquiv` (the last
row is `(u)`) and `detPower_tateScalarEquiv` (`|det|_ℂ^s = |u|^(2s)`). `dualFunction_apply`
shows that in rank one `W̃(g) = W(ᵗg⁻¹)`, because the long Weyl element of `GL₁` is `1`.

## Character algebra

- `character_shift`: for `d` of weight `m` and exponent `t`, `v ∈ ℂ`, `u ∈ ℂˣ`,
  `|u|⁻² · χ_d(u) · v · |u|^(2s) = v (u/|u|)^m |u|^(2(s+t)-2)`.
- `mul_character_apply`: `χ_{c·c'}(u) = χ_c(u) χ_{c'}(u)` (by definition).
- `inv_mul_character_apply`: `χ_{(c·c')⁻¹}(u) = χ_c(u)⁻¹ χ_{c'}(u)⁻¹`.
- `character_inv_apply`: `χ(u⁻¹) = χ(u)⁻¹`.

## The integrands on the line

The section `Integrands` assumes `hW : ∀ g, W g = C · χ_c(det g)` and the matching `hW'`
for `W'`. Write `m` and `t` for the weight and exponent of `c.mul c'`.

- `extend_equalIntegrand`: for every `z ∈ ℂ`,
  `|z|⁻² · (unitsExtend (complexEqualIntegrand W W' Φ s))(z) = C C' · integrand (lineSchwartz Φ) m t s z`.
  At `z ≠ 0` this evaluates `W(g) W'(g) Φ(e_n g) |det g|_ℂ^s` at the scalar matrix `g = z`
  and applies `character_shift` to `c.mul c'`. At `z = 0` both sides are `0`.
- `extend_dualIntegrand`: the same for the dual integrand
  `W̃(g) W̃'(g) Φ̂(e_n g) |det g|_ℂ^s`, with right side
  `C C' · integrand (tateFourier a |a| (lineSchwartz Φ)) (-m) (-t) s z`. It uses
  `dualFunction_apply`, `det(ᵗg⁻¹) = (det g)⁻¹`, `complexFourierTransform_const` and
  `character_shift` for the inverse character `(c.mul c').inv`, which has weight `-m` and
  exponent `-t`.
- `equalIntegral_eq`: if `D.measure = κ • (quotientUnits.symm)_* unitsHaar`, then for every
  `s ∈ ℂ`, `complexEqualIntegral D W W' Φ s = κ/2 · (C C') · zeta (lineSchwartz Φ) m t s`.
  The proof uses `integral_eq` from `ComplexRankZeroHaar`, the pointwise identity above and
  `integral_two_smul`. The factor `1/2` appears because `zeta` uses `2 ·` Lebesgue measure.
- `equalDualIntegral_eq`: under the same hypothesis,
  `complexEqualDualIntegral a D W W' Φ s = κ/2 · (C C') · zeta (tateFourier a |a| (lineSchwartz Φ)) (-m) (-t) s`.
- `integrable_equalIntegrand`: if also `κ ≠ 0` and the Tate integrand
  `integrand (lineSchwartz Φ) m t s` is integrable for `2 ·` Lebesgue measure, then the
  integrand of `Ψ(s; W, W', Φ)` is `D.measure`-integrable. The proof uses `integrable_iff`
  from `ComplexRankZeroHaar`.
- `integrable_dualIntegrand`: the same for the dual integrand, assuming integrability of
  `integrand (tateFourier a |a| (lineSchwartz Φ)) (-m) (-t) s`.

## Rank-one factors

- `complexPairBlocks_singleton`: the pair blocks of `[c]` and `[c']` are `[c.mul c']` (by
  definition).
- `complexPairLFactor_singleton`: the denominator of `complexPairLFactor [c] [c']` at `s`
  is `Γℂ(s + (t + |m|/2))⁻¹` (the Library's `complexLFactor_singleton`).
- `inv_mul_exponent`, `inv_mul_weight_natAbs`: `c.inv.mul c'.inv` has exponent `-t` and
  the same `|m|` as `c.mul c'`.
- `complexPairEpsilon_singleton`: for `c₀ > 0`,
  `complexPairEpsilon [c] [c'] a c₀ s = c₀ (a/|a|)^m |a|^(2(s+t-1)) i^|m|`. The proof starts
  from the Library's `ComplexCharacterData.coe_epsilon` and `character_eq`, and uses
  `|a|^(2t) |a|^(2(s-1)) = |a|^(2(s+t-1))`.
- `reflectedGammaComplex t q`: the entire function `s ↦ Γℂ(1 - s - t + q)⁻¹`, as a
  `ReciprocalEntire`. It is used only to name the discrete set of poles of
  `Γℂ(1 - s - t + q)`.

## The main theorem

`complexEqual_rankZero` assumes `hTate : ComplexArchimedeanTateStatement`, `a ∈ ℂˣ`,
character data `c, c'`, `D : ComplexQuotientMeasureData 0`, `hW`, `hW'` as above and a
Schwartz function `Φ` on `ℂ¹`. Its conclusion is exactly the conclusion of
`ComplexLocalEqualFunctionalEquationStatement` at `r = 0`, `d = [c]`, `d' = [c']`. That is,
there are `σ ∈ ℝ` and `M, Md : ℂ → ℂ` such that:

1. both integrands are `D.measure`-integrable for `Re s > σ`;
2. `s ↦ Ψ(s; W, W', Φ)` and `s ↦ Ψ(s; W̃, W̃', Φ̂)` are holomorphic on `Re s > σ`;
3. `M` and `Md` are meromorphic on `ℂ` and agree with the two integrals on `Re s > σ`;
4. for `s` outside a discrete subset of `ℂ` (the filter `codiscrete ℂ`),
   `L(s, [c] × [c']) · Md(1 - s) = ω_{c'}(-1)^0 · ε(s, [c] × [c'], ψ_a) · L(1 - s, [c⁻¹] × [c'⁻¹]) · M(s)`,
   where each `L`-factor is the inverse of the corresponding `.denominator` and `ε` uses
   the constant `c₀ = |a|`.

The proof follows these steps.

- `exists_measure_eq` (from `ComplexRankZeroHaar`) gives `κ ≠ 0` with
  `D.measure = κ • (quotientUnits.symm)_* unitsHaar`.
- From `hTate`: the continuation part gives a meromorphic `Z` with
  `ExtendsIntegral Z (lineSchwartz Φ) m t`. The functional-equation part, applied with
  `c = |a|`, gives a Schwartz function `g` equal to `tateFourier a |a| (lineSchwartz Φ)`,
  together with Tate's local functional equation for `Z` and any `Y` with
  `ExtendsIntegral Y g (-m) (-t)`. The continuation part gives such a `Y`. The
  integrability part gives integrability of both Tate integrands on their half-planes.
- Set `σ = |Re t|`, `K = κ/2 · C C'`, `M(s) = K · Z(s)` and `Md(s) = K · Y(s)`. Then
  `Re s > σ` implies `Re(s + t) > 0` and `Re(s - t) > 0`.
- Integrability follows from `integrable_equalIntegrand` and `integrable_dualIntegrand`.
- Holomorphy: `equalIntegral_eq` and `equalDualIntegral_eq` (with `⇑g` substituted for the
  Fourier transform) write both integrals as `K` times `zeta (lineSchwartz Φ) m t` and
  `zeta g (-m) (-t)`. These are differentiable on the half-planes by
  `ComplexTate.differentiableAt_zeta`.
- Meromorphy: `Z` and `Y` are meromorphic in normal form, so they are meromorphic, and so
  are their constant multiples.
- Agreement on `Re s > σ`: from the two integral formulas and the continuation properties
  of `Z` and `Y`.
- Functional equation: by `eventually_codiscrete_iff_forall_eventually_nhdsNE` it suffices
  to prove it in a punctured neighbourhood of every `s₀`. There, three things hold together:
  Tate's functional equation
  `Y(1-s) / Γℂ(1-s-t+|m|/2) = |a| (a/|a|)^m |a|^(2(s+t-1)) i^|m| · Z(s) / Γℂ(s+t+|m|/2)`,
  `Γℂ(s+t+|m|/2) ≠ 0` and `Γℂ(1-s-t+|m|/2) ≠ 0`. The nonvanishing comes from the Library's
  `ReciprocalEntire.denominator_eventually_ne_zero` for `gammaComplex.shift (t + |m|/2)`
  and `reflectedGammaComplex t (|m|/2)`. Since `[c].map inv = [c.inv]`, the lemmas
  `complexPairLFactor_singleton`, `inv_mul_exponent` and `inv_mul_weight_natAbs` give
  `L(s, [c] × [c']) = Γℂ(s + t + |m|/2)` and
  `L(1 - s, [c⁻¹] × [c'⁻¹]) = Γℂ(1 - s - t + |m|/2)`. The sign `ω_{c'}(-1)^0` is `1`, and
  `complexPairEpsilon_singleton` identifies `ε` with the factor in Tate's equation.
  Clearing denominators (`field_simp`, with the two Gamma values generalized to variables)
  gives the claim.

## Provenance

The functional equation of the rank-one Rankin–Selberg integral over `ℂ` is Tate's local
functional equation at a complex place (Tate's thesis; Cassels–Fröhlich 1967, Chapter XV).
The Library states it as `ComplexArchimedeanTateStatement`. It is the case `n = 1` of
Jacquet, *Archimedean Rankin–Selberg integrals* (2009), Theorem 2.1. The reduction of the
`GL₁(ℂ) × GL₁(ℂ)` integrals to Tate integrals of the line restriction of `Φ` and of its
Fourier transform is internal to this project. It follows the real version
`RealRankZeroLocal`.
