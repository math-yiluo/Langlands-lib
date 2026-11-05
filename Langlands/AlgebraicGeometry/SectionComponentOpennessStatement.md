# Openness of fibre components meeting a section

`Langlands.AlgebraicGeometry.SectionComponent.FlatFinitePresentationOpennessStatement.{u}`
states the openness assertion in EGA IV, Troisième partie, Corollary 15.6.5.
For arbitrary schemes `X` and `Y` and an actual morphism `f : X → Y` with
section `e : Y → X`, assume `f` is flat, locally of finite presentation,
quasi-compact, quasi-separated, and geometrically reduced. Then
`componentSet f e he` is an open subset of `X`.

The three conditions `LocallyOfFinitePresentation f`, `QuasiCompact f`, and
`QuasiSeparated f` express finite presentation of the morphism. None is
discarded. There is no finiteness, separation, reducedness, or noetherian
assumption on the base `Y`. Mathlib's `GeometricallyReduced f` states
reducedness after every field-valued base change; its fibre
characterization is the geometrically reduced fibre condition of the
source. The class `Flat f` is required separately.

The subset is the existing `componentSet`: in each actual residue fibre
`X_y`, take the topological connected component of the point induced by the
section, and take the union of its images in `X`. The statement uses the
actual pullback section and residue fibres, with all schemes in arbitrary
universe `u`.

The source is A. Grothendieck and J. Dieudonné, *Éléments de géométrie
algébrique IV, Troisième partie* (1966), Corollary 15.6.5, printed
pp. 238–239 (one-based PDF pages 237–238 in the retained file).
Registered source `ega-iv3-grothendieck-dieudonne-1966`, SHA-256
`f365212b38f20608ba34c21ae3ee40bbae1b42d9d3dff01a85356f9cc819c23e`.
The Lean proposition records the final openness consequence of the
corollary. It does not record the stronger neighbourhood assertion for a
single geometrically reduced selected component.

The original EGA IV, Quatrième partie, List III of errata was checked at
the §15 entries, printed pp. 347, 357–358 (one-based PDF pages
346, 356–357). It corrects 15.6.1, 15.6.3, 15.6.7, and 15.6.10, with
no correction to 15.6.5. This source is registered as
`grothendieck-dieudonne-ega-iv4-1967`, SHA-256
`b4277fb99c6edf8feec5b01f54368e4b8521bcd52871316c0edf6ff4ae69389e`.

This file defines a proposition and supplies no proof of openness.
Applying it to smooth morphisms still requires the finite-presentation
hypotheses. Applying it to an arbitrary smooth group scheme therefore
requires a local finite-presentation reduction and the group argument;
neither is asserted here. Relative group-component existence, geometric
connectedness, normality, and arbitrary base change remain separate proof
obligations.
