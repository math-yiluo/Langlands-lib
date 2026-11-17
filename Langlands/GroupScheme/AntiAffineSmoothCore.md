# Smooth connected geometric core of an anti-affine algebraic group

This is an internal supporting construction for the smoothness step of anti-affine quotient existence. It retains actual group schemes and maps throughout.

`AntiAffineSmoothCore N` packages an actual smooth connected closed subgroup of `N`, an actual inclusion, and a homeomorphism of underlying spaces whose map is that inclusion. It does not state that the inclusion is a scheme isomorphism.

The helper `IsAntiAffine.connectedSpace` proves connectedness of every anti-affine field group without finite-type or smoothness hypotheses. The structure map identifies the actual global-functions ring with the field. A nontrivial clopen partition would make this domain a product of two nonzero rings, by the structure sheaf's disjoint-open product comparison. The identity section supplies nonemptiness.

For a group locally of finite type over a perfect field, `IsAntiAffine.smoothCore` uses the published actual `reducedSubgroup` and its canonical closed inclusion. The existing smoothness theorem for the reduction supplies smoothness; the reduction inclusion is a surjective closed embedding, so it identifies the underlying topological spaces and transports the connectedness just proved.

`IsAntiAffine.geometricSmoothCore` first base-changes an algebraic anti-affine group over any field to an algebraic closure. Quasi-compactness and the published field-group separatedness theorem supply the qcqs hypotheses for the existing anti-affineness base-change result. The perfect-field construction then applies to the actual base-changed group.

The provenance is internal assembly of `AntiAffineBaseChange`, `ReducedSubgroup`, field-group separatedness, and the elementary sheaf/topology argument in `AntiAffineConnected`. This supplies the smooth connected subgroup used in the source proof of SGA 3 VI_B Lemma 12.3, without claiming a represented finite quotient by it. Smoothness of the original group and representability of that finite quotient remain open.

The helper `smooth_of_affine_smooth_surjection` isolates the remaining use of a quotient. Any actual smooth surjective map from an anti-affine group to an affine scheme is constant at its value on the identity section. Smooth surjectivity makes the map an epimorphism, so this constant value is inverse to the target's structure map. That structure map is consequently an isomorphism, and composing it with the supplied smooth map proves smoothness of the original group. No quotient representability is inferred here.
