# Ambient retractions for closed vector subgroups

This internal construction gives a dimension induction for actual closed
subgroups of standard vector groups over an arbitrary field `k` in universe
`u`. It separates the categorical induction from the later construction of a
smaller ambient vector envelope. No smoothness, reducedness, connectedness,
characteristic, infinitude or perfection hypothesis is imposed on the
subgroups used in the induction.

For a base morphism `b : S′ ⟶ S`, relative objects `A`, `Z` over `S′`, a map
`z : Z ⟶ A`, and a group homomorphism `l : L ⟶ H` over `S`,
`CapturesPointedMaps b A Z z l` says that every `a : A ⟶ H` after base change
with `z ≫ a = 1` factors through the changed homomorphism `l`. Its range uses
actual morphisms of relative schemes, with no restriction on the test objects.

`capture_via_intersection` passes this property through the actual
scheme-theoretic intersection of `i : H ⟶ G` with `s : V ⟶ G`.
The inputs are a retraction `t : G ⟶ V` with `s ≫ t = id`, capture of the
pointed maps of `H` by `s` in the ambient group, and capture of the pointed
maps of the intersection by `l`. Base change preserves the pullback defining
the intersection. A range witness in `V` is pointed because of the retraction.
The pullback lift is pointed by its two projections, so the capture hypothesis
on the intersection applies. Composing its range witness with the first
projection proves capture in `H`.

`exists_capturing_ambientRetraction_of_lowering` assumes a lowering rule:
each proper closed embedding of a group `H` in a vector group of dimension
`n` has a vector envelope of dimension `m < n` with a retraction from the
whole ambient vector group, capturing the specified pointed maps after `b`.
It concludes that any closed embedding `i : H ⟶ Vₙ` has maps
`l : Vᵣ ⟶ H` and `t : Vₙ ⟶ Vᵣ` with `l ≫ i ≫ t = id`, where `l` captures
those pointed maps in `H` itself. The proof is strong induction on `n`.
For an isomorphism it uses the inverse. Otherwise it intersects with the
smaller envelope and applies the induction hypothesis to the closed second
projection. The pullback condition and the two retraction identities give
the composed retraction; `capture_via_intersection` gives capture.

The auxiliary `isAffine_of_closed_into_vector` obtains affineness from a
closed immersion into the affine standard vector group.

The provenance is internal: these results compose the published actual
subgroup-intersection, base-change and range interfaces with natural-number
induction. This unit retains the lowering rule as an explicit input. It does
not construct that rule or assert the unconditional vector-factor theorem or
affine-line constancy of a complement.
