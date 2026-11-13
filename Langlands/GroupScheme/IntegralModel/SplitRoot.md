# Integral root models from an integral split torus

Let `R` be a commutative domain and `K` its specified fraction field, in one
arbitrary universe `u`. Let `M : IntegralModel R K G` be smooth, and let
`i : S → M.group` be any homomorphism from a split torus over `Spec R`.
For every nonzero character `a` of `S`, this construction produces a smooth
affine integral root model with geometrically connected fibres and an actual
closed inclusion into `M.group`. No integral torus or ambient model existence
is asserted here; these are the explicit input data.

`integralGroup` and `integralHom` choose the actual root representative and
closed immersion constructed in `SplitRootSubgroupOverDomain`.
`integral_properties` retains full all-test representation of the intrinsic
root functor, affineness, smoothness and geometric connectedness. The chosen
generic group `genericGroup` is the actual pullback of this integral group to
`Spec K`, and `genericHom` is its base-changed inclusion followed by
`M.genericIso.hom`.

The theorem `isRepresentedBy_genericHom` proves that this generic group
represents the existing full root functor of the base-changed character and
the generic torus map `M.genericHom i`. It uses the existing arbitrary-base
root-functor base-change theorem, base change of all-test representation,
and transport by the actual generic-fibre isomorphism of the ambient model.
It is not only an identification of rational points.

`model` uses the integral root group and the identity identification of its
actual generic fibre. Smoothness implies its required flatness and local
finite type; affineness is already known. The inclusion `inclusion` is a
compatible `IntegralModel.Hom` extending `genericHom`, and remains closed.
The model is smooth and has geometrically connected fibres.

Finally `map_integralPoints_eq` identifies the model's point image in `G(K)`
with the intersection of `M.integralPoints` and the rational points of that
full generic root functor. The proof applies the existing closed-subgroup
integrality theorem to `integralHom`, uses the actual compatible model square
to identify the section-image homomorphisms, and uses all-test representation
to identify the generic image with the root functor's points.

This is internal derived content from the domain root construction, the
published root-functor base-change and transport results, and closed-subgroup
integral-point lifting. It supplies actual root models when an integral split
torus in a smooth ambient model is available. It does not construct this torus
or ambient model, identify the point intersection with a valuation filtration,
compare adapted zero subgroups, or prove the final parahoric-model theorem.
