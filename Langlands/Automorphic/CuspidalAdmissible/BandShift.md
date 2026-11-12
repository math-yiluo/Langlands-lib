# Shifting the determinant band by central elements

Module: `Langlands.Automorphic.CuspidalAdmissible.BandShift` (declarations in
`Langlands.Automorphic.OperatorDeterminantSlice`). Provenance: internal.

- `bandAt F n α`: the open band `α < |det| < 2α` of the actual quotient (`bandAt_one`:
  `α = 1` is the Library's `band`); it is open and measurable.
- `quotientDeterminantNorm_translate`: right translation by `g` multiplies the quotient
  determinant norm by `determinantNorm g`.
- `preimage_bandAt_translate`: if `determinantNorm g = α`, translation by `g` pulls `bandAt α`
  back to `band`.
- `enorm_toQuotient_translate_scalar`: for a realization with unitary central character `χ`,
  translation by a central scalar `z` changes the realized function by the phase `χ(z)`
  (`toQuotient_central`), so its norm is unchanged.
- `lintegral_bandAt` (**band shift**): for positive rank, `∫_{bandAt α} |f|² = ∫_band |f|²`.
  Take a central scalar of determinant norm `α` (`exists_scalar_determinantNorm`), use that
  translation preserves `quotientHaarMeasure` (`measurePreserving_translate`) and the
  preimage identity.
- `lintegral_wideBand_le`: the closed band `3/4 ≤ |det| ≤ 9/4` lies in
  `bandAt (7/10) ∪ bandAt (6/5)`, so its squared-norm integral is at most twice the band
  integral.
- `exists_lintegral_closedBand_le` (**closed bands cost a constant**): for `0 < m` and any `M`
  there is `N ∈ ℕ` with `∫_{m ≤ |det| ≤ M} |f|² ≤ N ∫_band |f|²` for every realized vector `f`.
  The compact interval `[m, M]` is covered by the open intervals `(2x/3, 4x/3)`, `x ∈ [m, M]`;
  take a finite subcover indexed by `s`. Since `(2x/3, 4x/3) = (α, 2α)` with `α = 2x/3 > 0`,
  the closed band lies in the union of the `bandAt α`; `lintegral_iUnion_le` and
  `lintegral_bandAt` give the bound with `N = #s`.
