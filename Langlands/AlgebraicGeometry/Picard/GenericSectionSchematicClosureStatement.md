# Integral birational closure of a generic section

`Langlands.AlgebraicGeometry.GenericSectionSchematicClosureStatement.{u}`
states a supporting step for the integral-base specialization of EGA IV,
fourth part, Proposition 18.10.19, printed p.167. The retained original is
`grothendieck-dieudonne-ega-iv4-1967`, SHA256
`b4277fb99c6edf8feec5b01f54368e4b8521bcd52871316c0edf6ff4ae69389e`.
This is a derived statement about Mathlib's schematic-image and birationality
constructions, rather than a verbatim translation of the proposition.

For an integral scheme `S` and a locally finite type, formally unramified
morphism `p : X ⟶ S`, take an actual generic section
`a : Spec S.functionField ⟶ X` whose composite with `p` is
`S.fromSpecStalk (genericPoint S)`. The statement says that the schematic image
`a.image` is integral and that its map `a.imageι ≫ p` to `S` is birational
over `S` to the identity of `S`. Here `Scheme.BirationalOver` means the
existence of an isomorphism between dense open subschemes compatible with
the two maps to `S`. Both schemes lie in the arbitrary universe `u`.

The source argument in Proposition 18.10.19 takes the reduced closure of a
rational section and makes it birational to the base. This formulation instead
uses the schematic image of the generic field map. A map from this one-point
spectrum is quasi-compact, so its schematic image is already integral.
Spreading the induced generic section of that image gives a partial section
on a dense open of `S`. Since its composite with the unramified map to `S`
is an open immersion, the partial section itself is an open immersion.
Its nonempty open image in the integral schematic image is dense, furnishing
the required compatible dense opens.

This statement adds no assumptions of quasi-compactness, quasi-separatedness,
normality, or noetherianity on `S` or `X`. It does not assert that the map from
the closure to `S` is an open immersion everywhere or that the generic section
extends to all of `S`; those require the remaining extension argument.
