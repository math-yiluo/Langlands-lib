# Recovering a cocharacter centralizer from its residue fibres

This internal construction combines dynamic representability, smoothness of
dynamic centralizers and the residue-fibre isomorphism criterion. It is a
derived result, with no separate external-source translation.

Let `G` be a smooth affine group scheme over an arbitrary scheme `S`, and
let `T` be a smooth commutative group scheme. Suppose `i : T → G` is monic
on underlying objects of `Over S`. Supply a cocharacter `χT : Gm → T`.
Assume that, for every point `s` of `S`, the actual dynamic centralizer of
the base change of `χT ≫ i` equals the range of the actual base change of
`i`, as subgroup functors on all test schemes over the residue field.

For any supplied representative `j : C → G` of that dynamic centralizer,
`torusFactorIsoOfResidueFibres` is the canonical factor map `T → C`,
promoted to an isomorphism. Its composite with `j` is `i`, as stated by
`torusFactorIsoOfResidueFibres_hom_comp`.

The centralizer representative is smooth by `dynamicBaseSmoothConnected`.
The commutativity of `T` provides the canonical factor map. On each
residue fibre, both `T` and `C` represent the same subgroup functor, so
uniqueness of monic representatives makes the pulled-back factor map an
isomorphism. `DynamicContainment.isIso_of_residueFibres` then makes the
factor an isomorphism on underlying schemes: its source is smooth and
its target is locally of finite type. The forgetful functors reflect
isomorphisms, giving the asserted group-scheme isomorphism.

Finally, `centralizer_eq_range_of_residueFibres` chooses a representative
using `dynamicBaseRepresentability` and applies this isomorphism to
identify the centralizer with the range of `i` on every test scheme over
`S`.

The results hold in every universe. No reductivity, closedness of `i`,
affineness of `T`, or connectedness hypothesis is imposed. The residue
comparison is an equality of subgroup functors over each residue field,
not merely an equality of rational-point subgroups.
