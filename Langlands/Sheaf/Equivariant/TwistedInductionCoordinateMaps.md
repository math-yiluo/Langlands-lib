# Transport in twisted induction coordinates

This internal categorical successor to `TwistedInductionCoordinates` computes the morphisms of the existing right Kan extension in its translated product coordinates. If a twisted arrow f from U to V has twist h, the coordinate indexed by g at U reads the coordinate indexed by g h⁻¹ at V and restricts it along the ordinary map from gU to (g h⁻¹)V with the same underlying map as f.

The structure-map equality for this ordinary map follows by cancelling h⁻¹h using the action convention. The inverse relabelling of gU followed by f equals this ordinary map followed by the inverse relabelling at V. Applying the actual right Kan extension and the naturality of its actual counit proves `map_projection`. No analytic or acyclicity assertion is made.

The category and morphism universes, the group universe, and the coefficient category universes are independent. Only `Group G`, `P.RespectsIso`, and existence of all pointwise right Kan extensions along the opposite inclusion are required; the transport arrow and its factorization do not need the Kan hypothesis. This result follows internally from `TwistedOver.Hom.w`, the translation action laws, and naturality of the existing Kan counit.
