# Generic and concrete atlases of the actual Picard pseudofunctor

This is an internal comparison of two published atlas conditions. Its
provenance is the actual `PicardGroupoid.relative` pseudofunctor, the generic
`Stacks.SchemeAtlas` condition, and the generic `PseudofunctorHomLift`
construction. It assumes no algebraicity or representability theorem.

For any actual scheme morphism `f : X → S` in universe `u`,
`relativeHomLift f` retains the actual line bundles in each fibre of
`PicardGroupoid.relative f` and applies `ULiftHom.{u + 1}` to its morphisms.
It therefore takes values in `Cat.{u + 1, u + 1}`, the universe required by
`Stacks.SchemeAtlas`. The original objects lie in universe `u + 1`, and their
actual isomorphism morphisms originally lie in universe `u`.

For actual line bundles `L` over `U ×ₛ X` and `M` over `T ×ₛ X`,
`pointFiberPresheafHomLiftIso f L M` gives the natural isomorphism

```
Stacks.pointFiberPresheaf (relativeHomLift f) (objUp (Core.mk L)) (objUp (Core.mk M))
  ≅ PicardGroupoid.pointFiberPresheaf f L M.
```

The construction first uses the generic natural point-fibre comparison. It
then precomposes with the same iterated-slice functor
`T.iteratedSliceBackward.op` and applies the functor associator. Thus both
sides use every actual scheme over `T.left` and every morphism in that
slice. An actual point retains its map to `U` and its actual bundle
isomorphism. Naturality preserves the original coherent restrictions.
The explicit `ULift` of the concrete Picard presheaf is exactly the lift
supplied by the generic comparison.

`isSmoothSurjectivePresentation_homLift_iff` transports each natural
representation through this presheaf isomorphism. In both directions it
keeps the very same scheme `P` over `T.left` and the very same smoothness
and surjectivity witnesses for `P.hom`. A generic fibre object is an
explicit hom lift of a `Core` object; forgetting these two wrappers
recovers an actual line bundle. Conversely, every actual line bundle gives
such an object by `Core.mk` and `ULiftHom.objUp`.

The two atlas comparison lemmas apply this presentation equivalence to the
existentially supplied atlas object. They retain the same actual scheme
`U`, the same actual line bundle, and, for
`hasLocallyFiniteTypeSmoothSchemeAtlas_homLift_iff`, the same witness that
`U.hom` is locally of finite type. These are equivalences of conditions
for arbitrary `f`; they require no properness or field hypothesis.

All declarations preserve the arbitrary universe `u`. Empty, nonreduced and
non-quasi-compact tests are included without restrictions. The comparison
constructs no atlas and proves no field Picard-stack algebraicity theorem.
The target `FieldPicardStackAtlasStatement` therefore still requires a
geometric existence proof; these lemmas remove only the generic/concrete
interface and universe-lift obligations.
