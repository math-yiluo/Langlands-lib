# Relative morphisms constant on connected components

Let `X` and `Y` be schemes over a base scheme `S`, with `X` locally Noetherian.
A family of base sections of `Y`, indexed by the actual connected components
of `X`, defines an actual relative morphism `X → Y`. Its restriction to each
open connected-component subscheme is the constant map given by the selected
section. No reducedness, connectedness, or nonemptiness assumption is made.

The construction `ComponentConstant.ofComponents` uses the published
`componentDesc` coproduct reconstruction of a locally Noetherian scheme.
The underlying scheme maps commute with the map to `S`, so they give a morphism
in `Over S`. The restriction formula follows from the coproduct identities.
Constant families give constant relative morphisms. Precomposition transports
the family along the actual continuous map on connected components.
Postcomposition and pairing commute with the construction.

The proposition `IsComponentConstant` records that a relative morphism has
this form. The module proves that it is preserved by precomposition,
postcomposition, and pairing, with locally Noetherian hypotheses on sources.

This is internal categorical infrastructure for algebraizing componentwise
constant rational matrix representations in the proof of Nagata's theorem.
Its provenance is the component coproduct construction in the imported
`Langlands.AlgebraicGeometry.LocallyNoetherianComponentCoproduct` module.
The proof uses identities of actual scheme morphisms throughout, including
any nilpotent structure of the component schemes.
