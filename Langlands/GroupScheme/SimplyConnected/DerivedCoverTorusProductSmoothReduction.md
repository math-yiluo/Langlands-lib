# Structural inputs for smooth derived-cover products

Authors: Worker 133 and Worker 1554.

This internal module connects two structural propositions to the existing
`DerivedCoverTorusProductSmoothStatement.{u}`. Its proof-producing definition
`derivedCoverTorusProductSmooth_of_preimage_of_surjectivity` proves the
conditional proposition `DerivedCoverTorusProductSmoothReductionStatement.{u}`:

```lean
DerivedCoverMaximalTorusPreimageStatement.{u} →
  DerivedMaximalTorusProductSurjectivityStatement.{u} →
    DerivedCoverTorusProductSmoothStatement.{u}
```

All three propositions retain their published meanings, with arbitrary
fields `k : Type u` and arbitrary universe `u`. This conditional result
requires proofs of both structural propositions before it gives the
unconditional target.

The composition helpers preserve the actual slice-product multiplication.
`isPullback_tensorHom_id` proves the cartesian square for tensoring a slice
morphism with an identity by its universal property.
`surjective_tensorHom_id` transports scheme surjectivity across that square.
`subgroupProductMap_precomp_first` expands the actual product map to identify
precomposition on its first factor. Composing the two surjective morphisms
then proves `surjective_subgroupProductMap_of_surjective_first`.
These helpers apply over any scheme base.

For the conditional reduction, the supplied
`IsSimplyConnectedDerivedCover d π` gives smooth affine groups `H` and `C`
and a surjective scheme morphism `π : C → D`. The supplied maximal torus
is smooth by `IsTorus.smooth`; its closed inclusion in affine `H` makes
it affine. The first structural input makes the full scheme-theoretic
pullback `subgroupIntersection (π ≫ d) i`, namely `C ×_H T`, a torus,
so it is smooth. The second input supplies scheme surjectivity of
`D ×_k T → H`. The first-factor composition helper transfers that
surjectivity through `π × id_T` to `C ×_k T → H`. Finally,
`smooth_subgroupProductMap_of_surjective_of_smooth_intersection` applies
to this actual product map.

The provenance is internal: the module combines the actual categorical
products, stability and composition of scheme surjectivity, torus geometry,
and the generic smooth-product criterion. It implements the reduction
proposed in the existing target's Markdown. Smoothness or étaleness of `π`
is not used; its finite central kernel may be nonsmooth in positive
characteristic. The two structural propositions remain proof obligations.
