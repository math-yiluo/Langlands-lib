# The Eisenstein series as an integral of a theta series

Module `Langlands.Global.RankinSelberg.EqualAnalyticEisenstein`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

The Library defines `E(g, Φ; s, χ) = Σ'_(γ ∈ P'(F)\GL_n(F)) F(γ g)` with the section
`F(g) = |det g|^s ∫_(𝔸^×) Φ(a e_n g) |a|^(ns) χ(a) d^×a` (`eisensteinSeries`,
`eisensteinSection`). This module expresses it through `Θ(Φ, ·)`.

## Results

- Countability instances for `F^×`, `GL_n(F)` and `P'(F) \ GL_n(F)`.
  `summable_of_tsum_enorm_ne_top`: a complex family with finite `Σ‖·‖ₑ` is summable.
- `lintegral_idele_unfold`, `integral_idele_unfold`:
  `∫_(𝔸^×) h = Σ_(f ∈ F^×) ∫_(D₁) h(f a)` (Mathlib `IsFundamentalDomain.lintegral_eq_tsum''`,
  `integral_eq_tsum''`, reindexed by `ratUnitEquiv`).
- `thetaNorm_eq_tsum_subtype`, `thetaSum_eq_tsum_subtype`: the theta series as sums over
  `F^n ∖ 0`.
- `sectionRow F r Φ γ g a = Φ(det a · e_n γ g)`, and `sectionWeight r χ s a = |a|^(ns) χ(a)`
  (`F^×`-invariant: `sectionWeight_ratUnit_mul`). `eisensteinSectionIntegrand_eq` writes the
  Library integrand as their product.
- **`tsum_lintegral_section`**: for every `F^×`-invariant `W ≥ 0`,
  `Σ_γ ∫_(𝔸^×) |Φ(a e_n γ g)| W(a) d^×a = ∫_(D₁) W(a) Θ⁺(Φ, ζ(a) g) d^×a`. Proof: unfold
  `∫_(𝔸^×)` over `F^×`, exchange sums and integrals (`lintegral_tsum`, `ENNReal.tsum_prod`), and
  reindex by `cosetRowEquiv` using `ideleOf_smul_lastRow`.
- **`tsum_integral_section`**: the same identity with `Φ`, `w` and `Θ`, if
  `∫_(D₁) |w| Θ⁺(Φ, ζ(a) g) < ∞`. That finiteness bounds every term (`integrable` per coset),
  makes the double family summable, and justifies `integral_tsum`.
- **`eisensteinSeries_eq`**: under that finiteness for `w = sectionWeight`,
  `E(g) = |det g|^s ∫_(D₁) |a|^(ns) χ(a) Θ(Φ, ζ(a) g) d^×a`.
- **`enorm_eisensteinSeries_le`**: always
  `|E(g)| ≤ ||det g|^s| ∫_(D₁) ||a|^(ns) χ(a)| Θ⁺(Φ, ζ(a) g) d^×a`.

## Provenance

This is the classical expression of the Eisenstein series through
`Θ'_Φ(a, g) = Σ_(ξ ≠ 0) Φ(a ξ g)` (Cogdell 2004, §2.3, printed pp.208–209; Jacquet–Shalika,
*On Euler products and the classification of automorphic representations I*, §4). The
proofs are internal.
