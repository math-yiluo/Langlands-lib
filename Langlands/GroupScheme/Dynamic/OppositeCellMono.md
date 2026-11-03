# Monomorphism of opposite dynamic multiplication

The imported definition
`Langlands.GroupScheme.SubgroupFunctor.cellMultiplication iU iP` is the
actual multiplication morphism
`(fst ≫ iU.hom.hom) * (snd ≫ iP.hom.hom)`. It is defined over any base scheme
for two group schemes mapping to a common ambient group scheme, in
[CellMultiplication](../SubgroupFunctor/CellMultiplication.md). Its definition
does not impose subgroup or dynamic hypotheses; the theorem below supplies
the monomorphism property when the two morphisms represent opposite dynamic
factors.

The theorem `Langlands.GroupScheme.Dynamic.mono_oppositeCellMul` proves that
multiplication from a represented opposite dynamic unipotent subgroup times a
represented dynamic parabolic to the ambient group is a monomorphism in the
category of schemes over the base.

The base is `Spec k` for an arbitrary field `k : Type u`. The structural morphism
of the ambient group scheme is affine. The two group-scheme morphisms `iU` and
`iP` represent, respectively, `Dynamic.unipotent` for the cocharacter obtained
by precomposition with `Gm.powerHom (-1)` and `Dynamic.parabolic χ`. The
conclusion is `Mono (SubgroupFunctor.cellMultiplication iU iP)`, definitionally the
monomorphism property for the displayed product morphism.
No smoothness, connectedness, reductivity or characteristic premise is used.

For arbitrary test schemes, suppose two morphisms into the product have the
same image. Write their component images as `ua`, `pa` and `ub`, `pb`.
The equality `ua * pa = ub * pb` gives
`ub⁻¹ * ua = pb * pa⁻¹`. Representability supplies the membership of each
component image in its subgroup functor. Closure under inverses and products
puts this ratio in both the opposite unipotent and the original parabolic.
The published
`Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic` makes the ratio
the identity, hence `ua = ub`; cancellation in the group gives `pa = pb`.
The monomorphisms supplied by representability then identify both original
components. The categorical product extensionality lemma identifies the two
test morphisms, proving the claimed monomorphism.

This is an internal consequence of the published all-test opposite-intersection
theorem in `Dynamic.OppositeIntersection` and elementary group cancellation.
The proof uses the underlying affineness supplied by
`isAffine_of_isAffineHom`. It requires no inference from field-valued points
to scheme morphisms. It provides the monomorphism part of an opposite-cell
argument; it does not claim that the multiplication is an open immersion or
that any classification target has been proved.
