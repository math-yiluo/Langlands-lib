# Unfolding the Eisenstein series in the equal-rank integral

This is an internal helper module for `EqualUnfoldingReduction.md`. Provenance: internal. It
formalizes the first half of the unfolding in Cogdell, *Analytic theory of L-functions for
GL_n* (2004), §2.3, printed p.210 (PDF p.213): "replace the Eisenstein series by its
definition, and unfold". The result turns the Library's global integral
`equalIntegral F χ φ φ' Φ s` over `Z_n(𝔸) GL_n(F) \ GL_n(𝔸)` (module `EqualIntegrals`) into the
integral of the kernel `φ φ' Φ(e_n ·) |det|^s` over `P_n(F) \ GL_n(𝔸)`, `n = r + 1`.
Namespace: `Langlands.Global.RankinSelbergGlobal.EqualUnfolding`. Notation is as in
`EqualUnfoldingSection.md` and `EqualUnfoldingCount.md`.

## The quotient measure (`Quotient`)

- `rationalDomain F n`: the Library's chosen fundamental domain of `GL_n(F)` in `GL_n(𝔸)`.
- `rational_mul_mem_slabSet_iff` and `preimage_image_mk_slabSet`: the slab `1 ≤ |det| < e^n` is
  left `GL_n(F)`-invariant (product formula), so it is saturated for `GL_n(F) \ GL_n(𝔸)`.
- `centralQuotientMeasure_eq`: the Library's `centralQuotientMeasure F n` is the quotient
  measure on `Z_n(𝔸) GL_n(F) \ GL_n(𝔸)` of Haar measure restricted to `slabSet ∩ rationalDomain`.
  The proof unfolds the Library definitions: the restriction of `rationalQuotientHaarMeasure` to
  `determinantSlab F n 1 (e^n)`, pushed to the central quotient.

## The integrands (`Products`)

- `equalSeriesProduct χ φ φ' Φ s = φ φ' E(·, Φ; s, χ)` and
  `equalSectionProduct χ φ φ' Φ s = φ φ' F(·, Φ; s, χ)`. The Library's `equalIntegrand` is
  `equalSeriesProduct` at quotient representatives (`equalIntegrand_eq`, by `rfl`).
- `equalSeriesProduct_central_mul`: `φ φ' E` is left invariant under `Z_n(𝔸) GL_n(F)` (the
  Library's `centralRationalSubgroup`) when `φ` and `φ'` are left `GL_n(F)`-invariant and
  `φ(a x) φ'(a x) = χ(a) φ(x) φ'(x)` for scalars `a`. The characters cancel by
  `eisensteinSeries_scalarPoint_mul`.
- `slab_indicator_equalSeriesProduct`: on the slab, `φ φ' E` at `x` is the sum over
  `q ∈ P'_n(F) \ GL_n(F)` of `φ φ' F(·, Φ; s, χ)` at `γ_q x`, and both sides vanish off the slab.
  The slab is `GL_n(F)`-invariant, so the indicator commutes with the translations.

## Step I

`eisenstein_unfolding` assumes:

- `hslab`: every band `{c < |a| ≤ e c}` of the fundamental domain of `GL_1(F)` has
  `ideleMeasure`-mass one;
- `φ`, `φ'` and `Φ` are measurable, and `φ`, `φ'` are left `GL_n(F)`-invariant;
- `φ(a x) φ'(a x) = χ(a) φ(x) φ'(x)`;
- the kernel `K = φ φ' Φ(e_n ·) |det|^s` is integrable on `mirabolicDomain F r`.

It concludes that `equalIntegrand F χ φ φ' Φ s` is integrable for `centralQuotientMeasure`, and
that `equalIntegral F χ φ φ' Φ s = ∫_{mirabolicDomain} K`.

Proof. `integrable_and_integral_slabFiber` gives integrability of `(x, a) ↦ K(a x)` on
`(D' ∩ slab) × 𝔸^×`. By `mul_eisensteinSection_eq_integral` its inner integral is
`φ φ' F(·, Φ; s, χ)`, which is therefore integrable on `D' ∩ slab`. The Library's
`integrableOn_tsum_and_setIntegral_eq` unfolds the sum over `P'_n(F) \ GL_n(F)` against the
fundamental domain `D'` of `P'_n(F)` and the domain `D` of `GL_n(F)`. With
`slab_indicator_equalSeriesProduct` this gives integrability of `φ φ' E` on `slab ∩ D`. By
`centralQuotientMeasure_eq` and `integrable_out_iff` that is the integrability of
`equalIntegrand`. The chain of equalities is: `equalIntegral` = `∫_{slab ∩ D} φ φ' E` =
`∫_{D' ∩ slab} φ φ' F` = `∫_{(D' ∩ slab) × 𝔸^×} K(a x)` (Fubini, `integral_prod`) =
`∫_{mirabolicDomain} K` (fiber computation).
