# Finite products for the etale-chart point topology

This internal construction proves the finite-product topological step
needed after decomposing a Weil restriction on all test schemes.
It derives the comparison from the published scheme finite-product
point homeomorphism and the functoriality and open-chart properties of
the etale-chart topology.

Let `W` and `X i` be algebraic spaces over a field `K`. A family of actual
space morphisms `π i : W → X i` is required to be a product cone for the
full underlying presheaves. Evaluation of this limiting cone at `Spec K`
constructs `finiteProductSpacePointsEquiv`. The projection formula says
its components are exactly the point maps of `π i`.

Assume the index is finite, `K` is a henselian nontrivially normed field,
and `W` and all the `X i` are quasi-separated and locally of finite type.
`finiteProductSpacePointHomeomorph` proves the point equivalence is a
homeomorphism for their independently defined etale-chart topologies.
No topology is defined by transport along this equivalence.

Forward continuity follows componentwise from functoriality of the point
topology. For the inverse, choose an etale finite type chart in each
factor. The product of their scheme sources is locally of finite type.
The full-presheaf product property supplies a map from that product
scheme to `W`. The published scheme point homeomorphism identifies its
point map with the inverse point equivalence composed with the product
of the chart point maps. This composite is continuous by the scheme-map
continuity theorem. Products of these chart maps are open, since the
index is finite. They cover all tuples of rational points, so their
images of inverse images of an open set prove continuity of the inverse.

The structural finite-product lemma proves closure under binary
products by pullback stability and composition, includes the terminal
relative scheme by the identity property, and applies finite-product
closure of object properties. Its local finite type specialization
generalizes the corresponding power argument in the published
`relativeEndomorphismPower_locallyOfFiniteType` construction to arbitrary
finite families.

This is a categorical and topological derivation. It does not prove
existence of a product or a Weil restriction: the full-presheaf limiting
fan and all stated geometric hypotheses remain inputs.
