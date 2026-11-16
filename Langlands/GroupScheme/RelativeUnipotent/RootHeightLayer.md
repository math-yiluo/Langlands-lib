# Exact-height additive coordinates

This internal construction derives additive exact-height coordinate homomorphisms from a `RootHeightChart`. A root parameter is injective because reading its ordered coordinates gives the tuple supported in its single coordinate. It therefore identifies the additive group of global functions with its actual root-factor subgroup. The same chart proves uniqueness of ordered products of all factor-subgroup elements.

`layerCoordinates` composes the actual quotient by the next height subgroup, the inverse of `HeightLayer.layerEquiv`, and extraction of the additive parameters in factors of the exact height. The positive-height hypothesis needed by the layer theorem is explicit. All constructions use every scheme test over the arbitrary commutative ring. Further geometric quotient claims will use a separate module.

`coordinateFactors` keeps the chart's factors at the exact height and replaces the others by the identity. `layerMap_coordinateFactors` proves that their product has the same successive-quotient class as the original point: higher factors vanish in the quotient and lower coordinates are already zero. Consequently `layerCoordinates_apply` identifies the quotient-defined homomorphism with reading exactly those coordinates in the original chart. This formula establishes additivity without assuming the original chart is a homomorphism.
