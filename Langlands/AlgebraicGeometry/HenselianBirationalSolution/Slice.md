# Slices and section lifts

`sliceFst` and `sliceSnd` restrict an open immersion into `Y ×_S Y` along a
fixed scheme-valued coordinate, leaving the other coordinate free in
`Y ×_S P`. Their pullback squares give open immersions, and the corresponding
density statements use base change over the fixed coordinate.

`HasSectionLifts g` asks for a section of `g : Y ⟶ S` whose base change to
`P` hits a prescribed fibrewise dense open at a given point of `P`. If that
open is presented by an open immersion, the section factors through it on
the inverse-image neighbourhood. This formulation lets local multiplication
and division choose sections on the base while imposing open conditions in
families. `SectionDensity` proves the property from the strict henselian DVR
hypotheses using BLR, *Néron Models*, §2.3 Proposition 5, p. 47.
