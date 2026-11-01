# Complete maps from disjoint unions of supplied affinoid atlases

Author: Worker 56. This is an internal construction using `AtlasDisjointUnion`
and the existing category of complete chosen bounded atlas maps. It introduces
no external source claim.

Let `K` be a complete normed ultrametric field and `I : Type z` a component
index type. Components `A i` lie in
`AffinoidAtlasPresentation.{u, max z v, max z w} K` and have nonempty charts.
The component-index universe is absorbed into both the space and chart-index
universes so that the constructed sum and its components lie in this same
category. Empty component spaces and an empty component-index type are allowed.
Original charts within a component may overlap and properly contain one another.

`inclusion` has the actual sigma injection as continuous base map, sends each
original chart index to its tagged index, and has the bounded identity as its
pullback. Same-component chart containment is exactly original containment;
the restrictions are unchanged. The three projection lemmas state these data.

For every family `f i : A i ⟶ B` into an arbitrary presentation in this category,
`desc` evaluates `f i` on the corresponding sigma component. The actual sigma
topology proves continuity from component continuity. Its chart index and bounded
pullback are precisely those of the original `f i`, as the projection lemmas
record. Nonempty source charts force equality of component tags under
containment. After transporting that tag, the original `f i` proves index
monotonicity and restriction compatibility, including proper chart containments.
No equality of different original chart indices is asserted.

`inclusion_desc` proves recovery of each entire component arrow.
`desc_inclusion` proves recovery of every arrow from the constructed sum.
The proofs compare continuous maps, index maps and dependent bounded pullback
families by the existing `Hom.ext`. Identity pullbacks disappear by actual
bounded algebra-map extensionality; equality on spectrum points is never used
to recover algebra maps. These laws construct `homEquiv`, whose forward map is
component restriction and whose inverse is the constructed descent.

`hom_ext` gives full-arrow extensionality from component restrictions.
`desc_unique` gives the unique descent for each family, and `desc_comp` proves
compatibility with every complete target arrow. `cofan` uses the actual
inclusions and sigma presentation. `cofanIsColimit` supplies its descent,
factorization and uniqueness laws, so this is a categorical coproduct in the
specified chosen-map category.

For arbitrary input presentations, this construction applies to their same-space
nonempty subpresentations from `AtlasNonemptyCharts`. There is no asserted
chosen-map isomorphism to a presentation that originally has an empty chart.
Arbitrary-source induction, analytic automorphism continuity, refinement
localization, the general analytic category and analytic sites remain separate.
