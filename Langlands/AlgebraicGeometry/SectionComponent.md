# Fibre components meeting a section

For arbitrary schemes `X` and `Y`, a morphism `f : X → Y`, and an actual
section `e : Y → X` with `e ≫ f = 𝟙 Y`, this file constructs the subset of
`X` obtained by taking in each residue fibre the connected component through
the section.

`fiberSection f e he y` is the actual morphism
`Spec κ(y) → X_y` defined by the pullback universal property from `e` and
`Spec κ(y) → Y`. Its projection to `X` is the composite through `e`, and its
projection to `Spec κ(y)` is the identity. `fiberPoint` evaluates this
morphism at the unique point of `Spec κ(y)`.

`componentSet f e he` is the union, inside `X`, of the connected components
of these `fiberPoint`s in the actual scheme fibres. The file proves that its
inverse image in each fibre is exactly the chosen connected component, and
that the entire range of `e` lies in the union. The fibre equality proof first
uses the structure morphism to identify the base points and then uses the
injectivity of the fibre inclusion to identify the fibre points.

The definition follows Grothendieck and Dieudonné, *Éléments de géométrie
algébrique IV, Troisième partie* (1966), Corollary 15.6.5, printed
pp. 238–239 (PDF pages 237–238 in the retained file). Registered source
`ega-iv3-grothendieck-dieudonne-1966`, SHA-256
`f365212b38f20608ba34c21ae3ee40bbae1b42d9d3dff01a85356f9cc819c23e`.
The construction of this subset does not need the flatness or finite
presentation assumptions of the corollary; those concern its openness.
The pullback and membership lemmas are internal consequences of the
definition and Mathlib's fibre homeomorphism.

EGA IV, Quatrième partie, List III of errata was checked at the entries for
§15 (printed pp. 347, 357–358): it corrects 15.6.1, 15.6.3, 15.6.7 and
15.6.10, with no correction to Corollary 15.6.5. This unit asserts no openness,
base-change compatibility, or geometric connectedness.
