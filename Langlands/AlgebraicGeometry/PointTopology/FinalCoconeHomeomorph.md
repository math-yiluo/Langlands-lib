# Final families of stage homeomorphisms

This is an internal categorical and topological construction for the direct-limit
step of Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Example 4.2, printed pages 9–10. Conrad passes from
compatible integral-model comparisons over enlarged supports to full adelic
points. The general lemma below isolates that assembly step; it does not itself
construct adelic rings or assert the whole adelic comparison.

## Objects and independently defined topologies

Let `F : I ⥤ Type u` and `G : J ⥤ Type u` be diagrams on small categories,
`H : I ⥤ J` a final functor, and `c`, `d` actual colimit cocones for `F`, `G`,
with witnesses `hc`, `hd`. Let `e : F ≅ H ⋙ G` be a natural isomorphism.
`finalCoconeIso` is the induced isomorphism of the actual cocone point types.
It transports `d` along the final functor and then along `e`, and uses
uniqueness of colimits. `finalCoconeIso_ι` and `finalCoconeIso_inv_ι` identify
its forward and inverse restrictions to each original stage.

For a family of stage topologies `τ`, `typeCoconeTopology F c τ` is defined
independently as the supremum of the topologies coinduced by all maps
`c.ι.app i`. No topology is transported along `e` or the colimit isomorphism.
`typeCoconeTopology_continuous_iff` proves that a map from this topology is
continuous exactly when its composites with all stage maps are continuous;
`typeCoconeTopology_continuous_ι` proves continuity of each stage map.

For the upper diagram assume each transition `G.map f` is continuous for its
given stage topologies `σ`. The theorem
`typeCoconeTopology_continuous_iff_final` proves that continuity from the upper
cocone topology can be tested only on the stages `H.obj i`. The proof chooses
an object of `StructuredArrow j H` for each upper stage `j`, using finality,
and factors its stage map through a transition to a stage in the final family.
This argument requires no injectivity of the stage maps and no separation
assumption on their spaces.

## The constructed homeomorphism and its proof

Assume in addition that each supplied map `e.hom.app i` is a homeomorphism
for the given topologies `τ i` and `σ (H.obj i)`. Then
`finalCoconeHomeomorph` equips `finalCoconeIso.toEquiv` with continuity in both
directions for the two independently defined cocone topologies. Forward
continuity follows by the lower stage criterion, the forward stage equation,
and continuity of each stage equivalence and upper cocone map. Inverse
continuity follows by the final-family criterion, the inverse stage equation,
and continuity of the inverse of each stage equivalence. The latter is
obtained from its open-map property using the actual inverse in `e`, so the
inverse coordinate formula remains literal.

`finalCoconeHomeomorph_ι` proves that the resulting homeomorphism on every
original lower stage is the given stage map followed by the upper cocone map.
The categorical proof uses Mathlib's colimit transport and uniqueness APIs;
the topological proof uses its supremum and coinduced continuity criteria.
No filteredness, local compactness, or extra continuity of lower transitions
is assumed in this generic construction.
