# Constructing inner discrepancy cocycles from a universal overlap equation

This internal adapter connects the published `LocalGroupIsoOverlap` and
`Rational.InnerDiscrepancy` APIs. Let `e : LocalGroupIso G H U` and let
`a : AutomorphicAction A G` over an arbitrary base scheme in universe `u`.
No field, covering, or reductivity hypothesis is used.

`hasInnerDiscrepancy_of_overlap` starts with an actual morphism
`δ : U ⊗ U ⟶ A.X` satisfying `e.HasOverlapDiscrepancy a δ`. For each pair
`b c : T ⟶ U`, it uses `lift b c ≫ δ` as the discrepancy point.
The published refinement formula proves that this point represents the
discrepancy after every morphism to `T`, which is exactly
`e.HasInnerDiscrepancy a`.

`hasInnerDiscrepancy_iff_overlap` also proves the converse. Apply all-test
innerness to the two projections from `U ⊗ U` to obtain `δ`. Evaluate its
representing equation after the projection from `(U ⊗ U) ⊗ G.X`, at the other
projection giving the universal group point. The resulting equation is
`HasOverlapDiscrepancy`.

If the action is faithful on all refinements, `overlapCocycle` applies the
published `innerCocycle` construction to this inner-discrepancy proof.
`overlapCocycle_hasDiscrepancy` gives its all-test discrepancy equation.
Naturality and uniqueness of a representing discrepancy point show in
`overlapCocycle_overlap` that its universal overlap morphism is exactly the
supplied `δ`. Finally, `overlapCocycle_unique` specializes the published cocycle
uniqueness theorem: any natural cocycle having this discrepancy equals the
constructed one. Neither naturality nor the cocycle identity is an input to
the constructor.

The provenance is internal: the proofs specialize, pull back, and compose the
two imported interfaces. This adapter assumes the local isomorphisms, action,
and universal discrepancy equation; it does not construct the structural
inputs required by quasi-split inner-form existence.
