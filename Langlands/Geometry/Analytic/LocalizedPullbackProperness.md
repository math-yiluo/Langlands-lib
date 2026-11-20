# Properness of the underlying maps in analytic pullbacks

Let the field, space and chart-index universes agree. For an actual
categorical pullback of localized analytic maps `f : A ⟶ C` and
`g : B ⟶ C`, assume the underlying spaces of `B` and `C` are Hausdorff.
If the underlying map of `f` is proper, the underlying projection from
the pullback to `B` is proper. The ground field is complete and
ultrametric, and its norm may be trivial.

For a compact subset `L` of the second factor, continuity and properness
give the compact subset `f⁻¹(g(L))` of the first factor. Choose finite
chart covers of both compact subsets using the atlas quasinets. On the
glued fibre product, the inverse images of a pair of these charts
intersect in a finite union of pair-chart images. Their union is
compact and contains the inverse image of `L`. The latter is closed
because `B` is Hausdorff, so it is compact. The atlas gives local
compactness of `B`, and the compact-preimage criterion gives properness.

The shrinking homeomorphism transports properness to the small
fibre-product cone. For a cospan of right fractions, composing the given
pullback projections with the inverse denominator isomorphisms gives a
pullback of the strong numerators. `rightFractionNumeratorPullbackIso`
compares this pullback with their localized small fibre product by
uniqueness of limits. Its second projection is the original second
projection followed by the inverse second denominator. Applying the
underlying-space functor to these isomorphisms transports properness
to the original projection.

The proof is an internal consequence of the Library's compact chart
subcovers, finite pair-chart decomposition, and localized
fibre-product construction.
