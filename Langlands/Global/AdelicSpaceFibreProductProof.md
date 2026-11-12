# Fibre products of adelic points of separated algebraic spaces

Author: Worker 105.

This module proves the fibre-product clause of Conrad's p.17 claims for both kinds of global
field. The source is Brian Conrad, *Weil and Grothendieck approaches to adelic points* (2011),
printed p.17: the topology on adelic points is compatible with fibre products. The clause is
the second conjunct of `NumberFieldSpaceAdelePointMapsStatement` and
`CurvePlaceSpaceAdelePointMapsStatement`. The module assumes that every adelic point of the
fibre product comes from a level.

## Declarations

Namespace `Langlands.Global.AdelicSpaceFibreProductProof`.

- `prod_induced`: a product of induced topologies is induced along the product map.
- `pullback_injective`: a pullback square of algebraic spaces is injective on sections into the
  product (`ext_app_of_isPullback`).
- `numberField_factor`, `curve_factor`: on every factor of a level, the topology of `P` is induced
  from `X × Y` (`CoordinateFibreProduct.fieldValued_eq_induced`, with the normed-field structures
  of `AdelicSpaceLocalFields`).
- `numberField_level`, `curve_level`: the same for the level topologies
  (`CoordinateFibreProduct.coordinate_eq_induced`).
- `numberField_stage`, `curve_stage`: the same for the stage topologies. Each stage is identified
  with a level of the base change to the `T`-integers, and the base-changed square is a pullback
  (`isPullback_baseChange`). The stage identifications are natural
  (`numberField_stageEquiv_map`).
- `numberField_fibreProduct`, `curve_fibreProduct`: **fibre products**. Suppose every adelic point
  of `P` comes from a level. Then `P(𝔸) → X(𝔸) × Y(𝔸)` is an embedding.
  - It is inducing by `FinalStage.isInducing_of_stages`. The stages of `X × Y` are the products
    of stages, which are open embeddings.
  - The saturation condition holds: if the image of `z ∈ P(𝔸)` comes from `X(A_T) × Y(A_T)`, the
    two components agree in `Z(A_T)`, because the stage map of the separated space `Z` is
    injective. They then define a point of `P(A_T)` mapping to `z`.
  - Injectivity is `pullback_injective`.
