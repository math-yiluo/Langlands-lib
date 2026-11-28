# The upper entry Haar measure in Levi coordinates of the open cell

Lean module: `Langlands.Global.RankinSelberg.RealSlotCellMeasure`.

This is a helper module of the proof of
`Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker.RealTemperedWhittakerBoundStatement`
(see `RealTemperedWhittakerBoundProof.md`). It states no `Prop`-valued statement; it proves lemmas
only. The content is internal and follows no literature source. Unprefixed names are in the
namespace `Langlands.Global.RankinSelbergGlobal.RealLeviStages`. `upperStepHaar r a` is the
self-dual upper entry measure on the upper unipotent group of `GL_{r+1}(ℝ)` for the scale `a`
(module `RealGodementStepChart`); `upperEntryCoordinates` are the upper entry coordinates of
`UpperUnipotentEntryCoordinates`; `vcl`, `shear`, `lowerCGL_shear` and `measurePreserving_shear`
are from `RealLeviBorel` and `RealLeviShear`. `w` is the long Weyl element.

## Upper entries from lower coordinates

- `revPair` identifies the upper entry pairs `(i, j)`, `i < j`, with the lower coordinates
  `(rev i, rev j)` of `CoordC (vcl (r + 1))`, and `upperOfLower Y` is the upper unipotent matrix with
  the entry `Y (rev i, rev j)` at `(i, j)` (`continuous_upperOfLower`).
- `weylLong_mul_upperOfLower`: `w · upperOfLower Y = n̄_B(Y) · w`, with `n̄_B(Y) = lowerCGL (vcl_monotone _) Y`.

## The Haar measure

- `haarScale r a = (√|a|)^{#pairs}` and `upperStepHaar_eq`: `upperStepHaar r a` is `haarScale r a`
  times the image of Lebesgue measure under `upperOfLower` (`pi_smul_volume`).

## Fubini in the Levi coordinates

For a monotone block function `cl`:

- `cellPt hcl Z X = upperOfLower (shear hcl (Z, X))` is the point of the open cell with block
  coordinates `Z` and opposite radical coordinates `X`; `weylLong_mul_cellPt`:
  `w · cellPt Z X = lowerMGL cl Z · lowerCGL hcl X · w`. `lowerCGL_zero`, `lowerMGL_zero`, and
  `cellPt_mul`: `cellPt Z X = cellPt Z 0 · cellPt 0 X`.
- `integral_upperStepHaar_eq`: for a continuous function `F` integrable for `upperStepHaar r a`, the
  function `(Z, X) ↦ F (cellPt Z X)` is integrable for the product of the Lebesgue measures, and
  `∫ F d(upperStepHaar r a) = haarScale r a · ∫_X ∫_Z F (cellPt Z X)`. The map
  `(Z, X) ↦ cellPt Z X` is measure preserving onto the image of Lebesgue measure under
  `upperOfLower` (`measurePreserving_shear`), and Fubini's theorem (`integral_prod_symm`) applies.
