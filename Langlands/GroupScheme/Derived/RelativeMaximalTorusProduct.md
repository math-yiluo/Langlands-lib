# Central products and relative maximal tori

This internal support module assumes a reductive group scheme `G` over any
scheme `S`, a central homomorphism `z : Z ⟶ G`, and a homomorphism `d : D ⟶ G`
whose multiplication `Z × D ⟶ G` is a supplied central isogeny. There is no
semisimplicity or maximal-central-torus assumption in this module.

For every closed relative torus `t : T ⟶ G` maximal on all residue fibres,
`RelativeDerivedTorus.intersectionFactor` is the actual homomorphism
`Z × (D ∩ T) ⟶ T`. Its composite with `t` is the prescribed multiplication.
The module proves that this factor is a central isogeny, a stronger property
than the isogeny required by the torus clause of the host correspondence.

The construction uses published all-test self-centralization of relative
maximal tori: the centre, hence the range of `z`, lies in `T`. The published
central-product restriction theorem identifies the factor as the pullback
of `Z × D ⟶ G` along `t`, and preserves central isogenies in that square.

`RelativeDerivedTorus.range_eq_of_intersections` proves that two such relative
maximal tori with equal ranges of their intersection projections into `D`
have equal ranges in `G`. The implemented proof postcomposes the equality by
`d`, obtaining equality of the full ambient intersection ranges. Both tori
have the central-product factorizations just constructed. The underlying
isogenies are effective epimorphisms, so the published fpqc product
reconstruction theorem gives equality on every test scheme. The small general
helper `SubgroupFunctor.range_comp_eq_of_range_eq` proves the postcomposition
step directly from the pointwise definition of range.

All results are derived internally from the imported Library results. This
module retains the supplied global central-product-isogeny hypothesis; it
does not establish that structural input or the inverse torus correspondence.
