# The determinant-band form of a cuspidal realization is a unitary form

This module proves that an actual cuspidal operator realization of `GL_n` over a
number field `F` with unitary central character is unitarizable in the sense of
`OperatorRealization.IsUnitarizable`. It produces one positive definite Hermitian
form on the realization space with three properties:

- it is invariant under the finite adelic translations;
- it is invariant under the standard compact translations at infinity;
- every real Lie direction acts skew-adjointly for it.

The form is the existing determinant-band `L²` form of
`Langlands.Automorphic.OperatorDeterminantSlicePairing`:

`⟨f, g⟩ = ∫_{band} conj (f q) · g q dq`.

Here the band is `1 < |det| < 2` in the rational quotient `GL_n(F) \ GL_n(𝔸_F)`,
and `dq` is the quotient Haar measure. The Library already supplied this form with
finite-action invariance (`finiteInvariantPositiveFormOfHaar`) and band square
integrability of cusp forms (`exists_band_cover`, `memLp_band_of_cover`). This
module adds the compact invariance and the real Lie skew identity.

This is the standard unitarity of the Petersson inner product on cusp forms. The
module does not follow a particular source, and its proof route is internal. It is
an internal helper for `CuspidalUnitaryContragredientExistenceStatement`. There the
contragredient of a unitary cuspidal realization `T` is to be realized on its complex
conjugate, with pairing built from this form.

## One-parameter subgroups (namespace `Langlands.Global.ArchimedeanGL`)

The archimedean matrices `ArchimedeanMatrix K n` form a complete normed real
algebra under the operator norm (`Matrix.Norms.Operator`). These are the same
instances that `smoothDifferential` uses.

- `oneParameter K n X t` is the unit `exp (t X)` of `ArchimedeanGL K n`. Its inverse is
  `exp (-(t X))`, proved by `NormedSpace.exp_add_of_commute`.
- `oneParameter_zero` gives `exp 0 = 1`.
- `hasDerivAt_oneParameter_val` gives the derivative `exp (t X) X`
  (Mathlib `hasDerivAt_exp_smul_const`).
- `continuous_oneParameter` proves continuity into the unit group, using
  `Units.continuous_iff` and continuity of `exp`.
- `infiniteOneParameter K n X t` is the same element in completion coordinates,
  via `archimedeanGLCoordinates`, with `_zero` and continuity lemmas.
- `hasDerivAt_smooth_oneParameter s X a t`: for a smooth function `s`, the function
  `u ↦ s (a · exp (u X))` has derivative `(smoothDifferential X s) (a · exp (t X))`
  at `t`. On invertible matrices `s` agrees with its coordinate extension, which is
  differentiable there. The chain rule (`HasFDerivAt.comp_hasDerivAt`) applies to the
  curve `u ↦ A · exp (u X)` with `A` the coordinates of `a`. Its derivative
  `A · (exp (t X) · X)` is exactly the direction `g · X` at
  `g = a · exp (t X)` used in the definition of `smoothDifferential`.

## Derivatives of realized vectors (namespace `Langlands.Automorphic.OperatorRealization`)

- `lieOperator X` abbreviates the actual real Lie operator
  `S.envelopingAction (envelopingGenerator (complexify X))`. This is the operator in
  `OperatorRealization.UnitaryForm`.
- `mul_ofInfinite_eq_pair` writes `x · ofInfinite c` as
  `pair (infinite x · c) (finite x)`.
- `evaluate_lieOperator_pair` identifies the value of `lieOperator X f` at
  `pair a b` with `smoothDifferential X` applied to the archimedean slice of `f` at
  `b`. It combines `evaluate_finiteSmoothEnvelopingAction` with
  `envelopingAction_real_generator`.
- `hasDerivAt_evaluate_oneParameter X f x t`: the function
  `u ↦ f (x · exp (u X))` has derivative `(lieOperator X f) (x · exp (t X))` at `t`.
  This is the slice derivative above, applied at the infinite component of `x`.

## Translation invariance and compact invariance (namespace `OperatorDeterminantSlice`)

- `translate_one`: translation by `1` is the identity on the quotient.
- The imported `toQuotient_compact` from `CuspidalUnitaryCompactForm` identifies
  the compact action `compactRepresentation k` on the quotient with right translation
  by `ofInfinite k`.
- `integral_inner_translate`: assume positive rank, a unitary central character `χ`,
  and a quotient measure preserved by all determinant-norm-one right translations.
  Then for every adelic matrix `a`, the band integral of
  `conj (f (q a)) · g (q a)` equals that of `conj (f q) · g q`. The proof is the
  argument of `inner_toL2_finite`, extended to an arbitrary `a`:
  - `exists_normalized_rightTranslate` gives a scalar idele `z` with
    `|det (z a)| = 1`;
  - the central character contributes the phase `χ(z)` of norm one, which cancels
    (`toQuotient_central`, `inner_phase`);
  - translation by `z a` preserves the band measure (`measurePreserving_translate_band`).

  Applied to `a = ofInfinite k`, this gives compact invariance. The determinant of
  `k` is never computed.

## Uniform square integrability (namespace `OperatorRealization`)

`exists_band_cover_uniform hS hlo Γ hΓ` is a variant of the Library's
`exists_band_cover` with one extra compact set `Γ`. It produces a measurable set `t`
of adelic matrices with two properties:

- `t` meets the rational orbit of every matrix with determinant norm in `[lo, hi]`;
- for every left-invariant measure that is finite on compacts, every realized vector
  `f`, and every function `Φ` with
  `Φ x ≤ ‖f (x c)‖ₑ` for some `c ∈ Γ` (depending on `x`), the integral `∫⁻_t Φ²` is
  finite.

The covering set and its proof are those of `exists_band_cover`: Siegel
decomposition, lattice torus translates of a compact set, and the summable bound
`summable_sq_lattice_bound`. The only change is that the chamber decay estimate
`exists_chamber_decay` is applied on the compact set `Q₁ · Γ` instead of `Q₁`. Hence
the bound on each translate `a_m Q₂` holds uniformly for right translates by `Γ`.

## Supremum functions (namespace `OperatorDeterminantSlice`)

- `lintegral_band_le_cover_of_continuous` and `memLp_band_of_continuous` are the
  Library's `lintegral_band_le_cover` and `memLp_band_of_cover`, stated for an
  arbitrary continuous real function `φ` on the quotient instead of a realized
  vector. Rational orbits are compared through
  `LeftCosetSpace.lintegral_restrict_discreteQuotientMeasure_le`, and the matrix Haar
  measure through `setLIntegral_map`.
- `curve X s = ofInfinite (exp (s X))` is a continuous curve with `curve X 0 = 1`.
- `continuous_toQuotient_translate`: `(q, s) ↦ f (q · c s)` is jointly continuous for
  every continuous curve `c`. The proof uses the open quotient map
  `mk × id` (`IsOpenQuotientMap.prodMap`) and continuity of evaluation and
  multiplication upstairs.
- `supNorm X h q` is the supremum of `‖h (q · exp (s X))‖` over `s ∈ [-1, 1]`.
  - It is continuous (`IsCompact.continuous_sSup`).
  - It bounds every such value (`norm_le_supNorm`) and is nonnegative.
  - It is attained at some `s` (`exists_supNorm_eq`, via `IsCompact.sSup_mem`).
- `memLp_supNorm hS X h`: for a cuspidal realization, `supNorm X h` is square
  integrable on the band. Apply `exists_band_cover_uniform` with
  `Γ = curve X '' [-1, 1]`. The attained supremum supplies the required `c ∈ Γ`.

## Skew-adjointness and the unitary form (namespace `OperatorDeterminantSlice`)

- `integrable_inner_toQuotient`: the pointwise Hermitian product of two band `L²`
  vectors is integrable (`MemLp.integrable_mul` with `norm_inner_le_norm`).
- `integral_inner_lieOperator_add`: for a cuspidal realization with unitary central
  character and band-square-integrable vectors, every real Lie direction `X`
  satisfies

  `∫_{band} conj ((X f) q) · g q + ∫_{band} conj (f q) · (X g) q = 0`.

  Proof: put `G s q = conj (f (q · c s)) · g (q · c s)` with `c = curve X`.
  1. By `integral_inner_translate`, `s ↦ ∫ G s` is constant.
  2. By `hasDerivAt_evaluate_oneParameter`, together with `HasDerivAt.star` and the
     product rule, `s ↦ G s q` has derivative
     `G' s q = conj ((X f)(q c s)) · g (q c s) + conj (f (q c s)) · (X g)(q c s)`.
  3. For `|s| < 1`, `‖G' s q‖` is bounded by
     `supNorm (X f) · supNorm g + supNorm f · supNorm (X g)`. This bound is integrable
     because each supremum function is band `L²` (`memLp_supNorm`).
  4. Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le` differentiates under
     the integral at `s = 0`. Since the integral is constant, `∫ G' 0 = 0`.
  5. At `s = 0` the translation is the identity, and the integral splits into the two
     stated terms.
- `unitaryForm hn hS χ hχ hSχ hL2 : S.UnitaryForm` packages the result. Its finite
  form is `finiteInvariantPositiveFormOfHaar`. Compact invariance comes from
  `toQuotient_compact` and `integral_inner_translate`. Real skewness comes from
  `integral_inner_lieOperator_add`, after rewriting both inner products by
  `inner_toL2`. `unitaryForm_inner` records that its inner product is the band
  integral.

## Main theorem (namespace `Langlands.Automorphic.CuspidalOperatorRealization`)

`isUnitarizable_of_hasUnitaryCentralCharacter T hT`: for
`[CompactSpace (AdeleQuotient F)]`, every
`T : CuspidalOperatorRealization F r` with
`RelativeWeilGroup.HasUnitaryCentralCharacter T` satisfies
`T.realization.IsUnitarizable`.

The proof extracts the unitary character `χ`. It equips `GL_{r+1}(𝔸_F)` with its
Borel structure, takes the band cover of `exists_band_cover` with `lo = 1` and
`hi = 2`, and obtains band square integrability of every vector from
`memLp_band_of_cover`. It then applies `unitaryForm` in rank `r + 1 ≠ 0`.

## Scope

The theorem uses no hypothesis beyond the actual cuspidal realization, its unitary
central character, and the compactness convention `[CompactSpace (AdeleQuotient F)]`
of the host statement. The form is algebraic: no Hilbert-space completion or
occurrence in `L²` is asserted. The result does not construct a contragredient. It
proves neither admissibility nor surjectivity of the induced pairing; those remain
separate obligations of the host task.
