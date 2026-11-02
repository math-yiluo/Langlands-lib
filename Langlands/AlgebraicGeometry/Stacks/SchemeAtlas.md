# Actual scheme presentations of a category-valued pseudofunctor

Fix a scheme `S : Scheme.{u}` and a contravariant category-valued
pseudofunctor `F` on the entire category of schemes over `S`. Its fibre
objects and morphisms live in universe `u + 1`. For an object `ξ` of its
fibre over `U`, and an object `η` over `T`, `pointFiberPresheaf F ξ η` is
a presheaf on **all** schemes over `T.left`.

At `p : Z → T.left`, its points consist of a morphism over `S` from
`Z`, equipped with the structure map `p ≫ T.hom`, to `U`, together with
an actual isomorphism between the pullback of `ξ` by that morphism and
the pullback of `η` by `p`. Isomorphisms remain part of the point data;
they are not replaced by existence or equality of isomorphism classes.
`PointFiberPoints` names this type, and `pointFiberPresheaf_obj` gives
the evaluation equation.

The definition uses the existing `PseudofunctorPointFiber.presheaf` on
the iterated slice `(Over S)/T`. Precomposing with Mathlib's
`T.iteratedSliceBackward` transports it to schemes over `T.left`. This
functor is the inverse of the standard iterated-slice equivalence. It
sends `p : Z → T.left` to the morphism
`(Z, p ≫ T.hom) → T` in `Over S`; restrictions are consequently the
ordinary coherent restrictions of the point-fibre construction.
No affine, reduced, quasi-compact or nonempty restriction is made on
any test scheme.

`IsSmoothSurjectivePresentation F ξ` requires that for every test `T`
and every actual object `η` over `T`, this presheaf is naturally
isomorphic to the lifted Yoneda presheaf of an actual scheme `P` over
`T.left`. It further requires that `P → T.left` be smooth and
surjective as a scheme morphism. The isomorphism is on the entire slice,
not just its field-valued points. Since the representation is in that
slice, its structure map is the projection of the represented fibre.

`HasSmoothSchemeAtlas F` asserts the existence of `U` and `ξ` with
this property. `HasLocallyFiniteTypeSmoothSchemeAtlas F` additionally
requires that `U → S` be locally of finite type. The forgetful lemma
retains the same `U`, `ξ` and represented fibres.

These are internal definitions of conditions and assert no existence
theorem. In particular, this module assumes and proves neither stack
descent nor the existence of an atlas for the Picard groupoid. The
presentation condition uses representation by schemes; it is suitable
for situations where this stronger representation is available. No
general equivalence with other definitions of algebraic stacks is
asserted. The provenance is the actual point-fibre construction,
Mathlib's iterated-slice equivalence, the lifted scheme Yoneda functor,
and the existing scheme properties `Smooth`, `Surjective` and
`LocallyOfFiniteType`.
