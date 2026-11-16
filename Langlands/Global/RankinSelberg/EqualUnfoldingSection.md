# The Eisenstein section and series in the equal-rank unfolding

This is an internal helper module for `EqualUnfoldingReduction.md`. Provenance: internal. It
proves the transformation laws and measurability of the Library's Eisenstein section
`eisensteinSection F χ Φ s` (written `F(g, Φ; s, χ)` below) and Eisenstein series
`eisensteinSeries F χ Φ s` (written `E(g, Φ; s, χ)`), both from `EqualIntegrals`. These are the
properties that Cogdell, *Analytic theory of L-functions for GL_n* (2004), §2.3, printed
pp.209–210, uses when he replaces the Eisenstein series by its definition and unfolds.
Namespace: `Langlands.Global.RankinSelbergGlobal.EqualUnfolding`. Notation is as in
`EqualUnfoldingScalar.md`: `a = ideleOf F z` for `z ∈ GL_1(𝔸)`, `diag(a, …, a) = scalarPoint F r z`,
and `χ(a)` is `Automorphic.centralIdeleCharacter F χ a`.

## Invariance and measures

- `leftInvarianceSubgroup f`: the subgroup `{g | ∀ x, f (g x) = f x}`, with
  `mem_leftInvarianceSubgroup_iff`.
- Instances `isMulLeftInvariant_ideleMeasure` and `sFinite_ideleMeasure` for the Library's
  `ideleMeasure F`.
- Instance `countable_rationalGL`: `GL_n(F)` is countable, because it injects into the discrete
  subgroup `GL_n(F)` of the second-countable group `GL_n(𝔸)`.

## The section (`Section`)

- `detPower_ne_zero`: `|det x|^t ≠ 0`.
- `eisensteinSectionIntegrand_scalarPoint_mul` and `eisensteinSection_scalarPoint_mul`:
  `F(diag(a, …, a) g, Φ; s, χ) = χ(a)⁻¹ F(g, Φ; s, χ)`. The proof substitutes `a' ↦ a a'` in the
  idele integral and uses left invariance of `ideleMeasure`.
- `eisensteinSection_congr`: the section depends only on `e_n g` and on `|det g|^s`. Hence
  `eisensteinSection_mirabolic_mul`: it is left `P_n(F)`-invariant.
- `eisensteinSection_eisensteinRational_mul`: it is left invariant under
  `P'_n(F) = Z_n(F) P_n(F)`. This uses `exists_scalarPoint_mul_inv` and the triviality of `χ` on
  principal ideles.
- `eisensteinCosetTranslate g`: the right translation `q ↦ q g` of `P'_n(F) \ GL_n(F)`, as an
  equivalence.
- `eisensteinSeries_rational_mul`: `E(k g) = E(g)` for `k ∈ GL_n(F)`. The summands are permuted
  by `eisensteinCosetTranslate` (`Equiv.tsum_eq`), and the change of representative is absorbed
  by `eisensteinSection_eisensteinRational_mul`.
- `eisensteinSeries_scalarPoint_mul`: `E(diag(a, …, a) g) = χ(a)⁻¹ E(g)`.
- `mul_eisensteinSection_eq_integral`: if `φ(a x) φ'(a x) = χ(a) φ(x) φ'(x)`, then
  `φ(x) φ'(x) F(x, Φ; s, χ) = ∫_{𝔸^×} K(diag(a, …, a) x) d^×a` with the kernel
  `K = equalKernel F φ φ' Φ s` of `EqualUnfoldingKernel.md`. Here `|det(a x)|^s = |a|^{n s} |det x|^s`
  and `e_n(a x) = a e_n x`. `equalKernel_scalarPoint_mul` is the pointwise form.

## Measurability (`Measurability`)

Row vectors carry their Borel σ-algebra through the local instances
`equalSectionRowMeasurableSpace` and `equalSectionRowBorelSpace`, as in the Library's
`WhittakerIntegrals`. For measurable `Φ`:
`measurable_eisensteinSectionIntegrand` (jointly in `(g, z)`), `measurable_eisensteinSection`
(by `StronglyMeasurable.integral_prod_right'`), `measurable_eisensteinSeries` (by
`StronglyMeasurable.tsum` over the countable index set) and `measurable_lastRow_comp`
(`x ↦ Φ(e_n x)`).
