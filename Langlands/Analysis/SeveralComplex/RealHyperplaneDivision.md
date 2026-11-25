# Division by products of real linear forms

Module `Langlands.Analysis.SeveralComplex.RealHyperplaneDivision` (namespace
`Langlands.Analysis.SeveralComplex`). It states and proves the proposition
`RealHyperplaneDivisionStatement` (proof `realHyperplaneDivision`); the
universe-polymorphic form is `exists_open_forall_tendsto_eq_rootProduct_mul`.
Everything is proved; there are no premises.

## Purpose and provenance

Helper for Lapid 2011, Proposition 6
(`Langlands.Global.EisensteinImaginaryAxisHolomorphyStatement`). Near a
point `λ₀ = e s₀` of `i𝔞_P^*`, the root-hyperplane description gives
`Q · E = h` holomorphic, with `Q s = ∏ β ∈ S, ℓ β (s - s₀) ^ m` a product of
linear forms that are real on the real structure. Lapid's proof (p.330) shows
that the wave-packet bound (19) is incompatible with a pole along such a
hyperplane. The route of `Langlands.Global.AdelicEisensteinImaginaryHolomorphyReduction`
uses the same mechanism in the form proved here:
if `h / Q` is square integrable on the totally real slice `s₀ + iℝⁿ` (for
averages of `h` over small sets of group elements, a bound that Lemma 10
gives), then `Q` divides `h` near `s₀`, and divisibility survives the limit
in which the averages shrink to a point.

Provenance: internal. The statement is standard several-complex-variables
analysis and is not taken from a source; its use is explained in
the Markdown of `Langlands.Global.AdelicEisensteinImaginaryHolomorphyReduction`. The quotient is an explicit Cauchy
integral along a generic real direction, so no several-variable Hartogs or
Osgood theorem (absent from Mathlib at the pin) is needed.

## Statement

Data: `n`, a finite set `S` of indices, complex linear forms
`ℓ β : (Fin n → ℂ) →ₗ[ℂ] ℂ` with `ℓ β ≠ 0` and
`(ℓ β (fun j => (x j : ℂ))).im = 0` for every real `x` (real on real points)
for `β ∈ S`, `m : ℕ`, `s₀ : Fin n → ℂ`, an open `W ⊆ ℂⁿ`, and `ρ > 0` with
`realSlice s₀ x ∈ W` for every real `x ∈ ball 0 ρ`, where
`realSlice s₀ x = s₀ + i x` (module `RealSliceIdentity`) and
`rootProduct S ℓ m s₀ s = ∏ β ∈ S, (ℓ β (s - s₀)) ^ m`.

Conclusion: there is an open `W'` with `s₀ ∈ W' ⊆ W` such that, for every
type `κ`, nontrivial filter `L` on `κ`, functions `H k` and `Hlim`:

- if `Hlim` is complex differentiable on `W`, eventually `H k` is complex
  differentiable on `W`, `H k → Hlim` locally uniformly on `W` along `L`,
- and eventually there is `C` with
  `∫ x in A, ‖H k (s₀ + i x) / Q (s₀ + i x)‖² ≤ C` for every compact
  `A ⊆ ball 0 ρ` (real `x`, sup norm) on which `Q (s₀ + i x) ≠ 0`,

then `Hlim = Q · H'` on `W'` for some `H'` complex differentiable on `W'`.
`W'` depends only on the data, not on `L`, `H`, `Hlim`. The case of a single
function is `L` a principal filter on a point with `H k = Hlim`.

Also in the module: `dense_setOf_rootProduct_ne_zero` (if every `ℓ β ≠ 0`,
`{s | Q s ≠ 0}` is dense) and `isOpen_setOf_rootProduct_ne_zero`, provided
for a density argument.

## Proof

1. Algebra (`ofRealVec`, `realPart`, `eq_realPart`, `realPart_ne_zero`): a
   form real on real points satisfies `ℓ (x) = Re ℓ (x)` for real `x`, and is
   nonzero on `ℝⁿ` if it is nonzero.
2. `exists_real_direction`: a real `v` with `v 0 = 1` and
   `Re ℓ β (v) ≠ 0` for all `β ∈ S`, since `ℝⁿ⁺¹` is not a finite union of
   proper subspaces (`Subspace.biUnion_ne_univ_of_top_notMem`), applied to the
   kernels and to `{x 0 = 0}`. (`S = ∅` is trivial, `Q = 1`; if `S ≠ ∅` then
   `n ≥ 1`.)
3. `rootProduct_line`: on the complex line `s₀ + i x + z (i v)`,
   `Q = c ∏ (z - τ)` over `S × Fin m` with `c ≠ 0` and real roots
   `τ β = -Re ℓ_β(x) / Re ℓ_β(v)`.
4. `cauchyQuotient H s = (2πi)⁻¹ ∮_{|z|=R} z⁻¹ H(s + z u) / Q(s + z u) dz`
   with `u = i v`. `differentiableOn_cauchyQuotient`: it is holomorphic in `s`
   wherever the circle `s + z u` lies in `W` and avoids the zeros of `Q`,
   by the parametric-integral criterion `differentiableOn_integral_of_bounded`
   (module `ParametricIntegral`) applied to the integrand in the angle.
5. `eq_mul_cauchyQuotient_of_line`: for a real `x` such that
   `t ↦ H/Q (s₀ + i(x + t v))` is square integrable on `(-T, T)` and the roots
   of step 3 lie in `(-T, T)`, the one-variable lemma
   `exists_eq_mul_prod_of_integrableOn` (module `SquareIntegrableDivision`)
   writes `H(s + z u) = Q(s + z u) φ(z)` on a disc, and Cauchy's formula
   (`DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul`) gives
   `H(s) = Q(s) · cauchyQuotient H s` at `s = s₀ + i x`.
6. `eqOn_mul_cauchyQuotient`: if almost every line is good, the holomorphic
   function `H - Q · cauchyQuotient H` vanishes almost everywhere on the real
   slice of a polydisc, hence everywhere there by continuity
   (`Measure.eqOn_open_of_ae_eq`), hence on the polydisc by the identity
   theorem on the real slice (`eqOn_zero_of_realSlice`).
7. `tendsto_cauchyQuotient`: locally uniform convergence `H k → Hlim` gives
   uniform convergence on the compact circle, and with `|Q| ≥ q₀ > 0` there,
   `cauchyQuotient (H k) s → cauchyQuotient Hlim s` (direct estimate, valid
   for any filter).
8. `exists_open_forall_tendsto_eq_rootProduct_mul`: choose `R₀` with
   `closedBall s₀ R₀ ⊆ W`, `Λ` bounding all `‖ℓ β‖`, `b₀ = min |Re ℓ_β(v)|`,
   `R = R₀ / (4(‖v‖ + 1))`, `T = min R (ρ / (4 (1 + ‖v‖)))` and
   `r = min (R₀/4, T, ρ/(2(1 + ‖v‖)), T b₀ / (2Λ))`; `W' = ball s₀ r`. These
   choices give the hypotheses of steps 4–6 for every function at once. For
   each `H k` (eventually), the compact-set bound and
   `integrableOn_of_forall_isCompact_le` (with the null closed set
   `{Q (s₀ + i x) = 0}`, `volume_setOf_rootProduct_realSlice_eq_zero`) give
   square integrability on `ball 0 ρ`; `exists_ae_integrableOn_line` (module
   `LineIntegrability`) gives almost every good line; step 6 gives
   `H k = Q · cauchyQuotient (H k)` on `W'`. Step 7 and uniqueness of limits
   give `Hlim = Q · cauchyQuotient Hlim` on `W'`, and `cauchyQuotient Hlim`
   is holomorphic there by step 4.

`differentiableOn_cauchyQuotient` and `tendsto_cauchyQuotient` are checked
with `maxHeartbeats 2000000`: unifying the two instance paths on `Fin n → ℂ`
(normed and plain `Pi` structures) is slow there.

## Scope

Scalar functions on `ℂⁿ` only. The hypothesis is square integrability on the
real slice through `s₀`; it says nothing about other points of `i𝔞_P^*`,
which are handled by applying the theorem at each point.
