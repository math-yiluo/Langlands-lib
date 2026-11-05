# Central tori in the quotient by a largest central torus

Author: Worker 1578.

This internal prerequisite for largest-central-subtorus base change uses the
published central extension theorem and the rigidity of normal split tori.
A normal closed torus in a smooth connected affine group becomes central over
a splitting field; geometric connectedness and faithfully flat reflection of
centrality give centrality over the original field.

For an fppf quotient `G → Q` with kernel a largest central torus `Z`, pull back
a closed central torus `T → Q`. The inverse image is a central extension of
`T` by `Z`, hence a torus. It is closed and normal in `G`, hence central by
the preceding lemma. Greatestness places it in `Z`, so its map to `Q`
vanishes. Faithful flatness of its projection to `T` shows `T → Q` vanishes.
The argument requires only smoothness, affineness and connectedness of `G`.

The pullback construction follows the implemented proof in the published
`Torus.CentralMaximalQuotientReduction`. Here centrality of the target torus
provides normality of its inverse image, replacing ambient maximal-torus
maximality by greatestness among central tori. This is a derived internal
argument; it introduces no additional structural premise.
