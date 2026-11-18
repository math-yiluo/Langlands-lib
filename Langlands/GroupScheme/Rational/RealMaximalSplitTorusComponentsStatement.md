# Maximal real split tori meet every real component

`Langlands.GroupScheme.RealMaximalSplitTorusComponentsStatement` is the
proposition that, for a smooth connected affine group scheme `G` over `ℝ`
and a chosen maximal real split torus `i : S.toGrp ⟶ G`, every real point `g`
belongs to the same connected component as the image of some real point `s`
of `S`.

The affineness instance is on the underlying scheme of `G`. Smoothness and
connectedness concern the structure morphism and underlying scheme space,
respectively. `IsMaximalSplitTorus i` makes `S` a split torus and `i` a closed
subgroup inclusion that is maximal among split subtori. The points of `S` and
`G` are the Library's `RingPoint` morphisms over `Spec ℝ`. The equality
`ConnectedComponents.mk (s ≫ i.hom.hom) = ConnectedComponents.mk g` takes place
in the connected-component quotient of `G(ℝ)`.

## Source and encoding

Armand Borel and Jacques Tits, *Groupes réductifs*, Publications Mathématiques de
l'IHÉS 27 (1965), Theorem 14.4 (Matsumoto), printed pp. 146–147, one-based PDF
pp. 93–94. Registered source `borel-tits-1965-groupes-reductifs`, SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.

The theorem states `G(ℝ) = G(ℝ)^0 S(ℝ)` and expresses this as surjectivity on
path components, as defined in §14.1. Since each path component lies in a
connected component, this gives the displayed equality for some `s` for each
`g`. The theorem starts with a connected real linear algebraic group in the
sense of §0.3 and includes the case of a nontrivial unipotent radical.
An affine smooth scheme over `ℝ` is of finite type and geometrically reduced.
For a group scheme of finite type, scheme connectedness implies geometric
connectedness by `Langlands.GroupScheme.geometricallyConnected_of_connected`.

The topology on `G(ℝ)` is the evaluation topology from
`Langlands.AlgebraicGeometry.PointTopology.AffineScheme`. This is the usual
real topology of §§9.1 and 14.1. A finite set of real algebra generators for
the coordinate ring gives a realization of `G(ℝ)` in finite-dimensional
real space. Its subspace topology is the evaluation topology, since every
other regular function evaluates as a polynomial in the chosen generators.
