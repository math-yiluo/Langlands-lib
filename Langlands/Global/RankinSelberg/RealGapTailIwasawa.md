# Haar measure in the triangular tail of the real unequal-rank chart

## Right Iwasawa coordinates

The private lemmas `upperEntry_rightTranslation_preserving` and `rightInvariant_entryHaar` show,
by the Library's finite triangular translation theorem, that right translation on the real upper
unipotent group preserves Lebesgue measure in the strictly upper entry coordinates. With the
Library's left Iwasawa Haar formula `RealLocalIwasawaHaar.realIwasawaHaar` applied to the inverted
measures, `exists_rightIwasawa_entryMeasure` gives every right invariant Haar measure on
`GL_n(ℝ)` as a positive multiple of the pushforward of Lebesgue measure on the logarithmic
diagonal coordinates and the unipotent entries times a Haar measure on the orthogonal group,
under `((y, x), k) ↦ k · u(x) · torus(y)`.

## The tail chart

* `tailModulus y = Π_{i<j} exp(y_j - y_i)^{-1}`, positive and measurable; `tailDiagonalMeasure q`
  is Lebesgue measure on `ℝ^{q+1}` with density `tailModulus`.
* Moving `torus(y)` to the left of `u` replaces the entry `(i, j)` of `u` by
  `exp(y_j - y_i)` times it; the scalar Haar change of variables gives the factor
  `tailModulus y` (`map_tailConjugation`).
* `tailChart ((y, u), k) = k · torus(y) · u`.

`RealGapTailIwasawaStatement`: for an additive Haar measure `μ` on `ℝ`, any Haar measure on
`GL_{q+1}(ℝ)` and any Haar measure `κ` on the orthogonal group there is `c > 0` with

`Haar = c • map tailChart ((tailDiagonalMeasure q × entryHaar μ (q+1)) × κ)`.

`realGapTailIwasawa` proves it from `exists_rightIwasawa_entryMeasure` (Haar measures on real
general linear groups are right invariant, `realMatrixHaar_symmetries`) by the shear moving the
torus to the left and the comparison of Lebesgue measure with the chosen entry product measure.

This is the real counterpart of the Library's `ComplexGapTailIwasawa`, with an arbitrary Haar
measure in place of the explicit complex density; it is the trailing-block measure calculation
after (10.5) in Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §10.2.
