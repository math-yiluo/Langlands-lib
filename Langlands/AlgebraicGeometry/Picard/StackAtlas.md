# Actual scheme presentations of the relative Picard groupoid

This is an internal definition of a condition on the published actual
line-bundle pseudofunctor. Its provenance is `PicardGroupoid.relative`,
the coherent point-fibre presheaf `PseudofunctorPointFiber.presheaf`,
Mathlib's iterated-slice equivalence, the lifted scheme Yoneda functor,
and the ordinary scheme properties `Smooth`, `Surjective` and
`LocallyOfFiniteType`. No existence theorem is asserted here.

Fix any scheme morphism `f : X → S`, a scheme `U` over `S`, and an actual
line bundle `L` on `U ×ₛ X`. For a test scheme `T` over `S` and an actual
line bundle `M` on `T ×ₛ X`, `pointFiberPresheaf f L M` is a presheaf on
all schemes over `T.left`. At `p : Z → T.left`, a point consists of a
morphism from `(Z, p ≫ T.hom)` to `U` in `Over S`, together with an
actual isomorphism between the two line bundles obtained by pulling `L`
and `M` back to `Z ×ₛ X`. The pullbacks are those of the relative
pseudofunctor. Isomorphisms are retained as data.

`PointFiberPoints` names this actual point type. The morphisms of schemes
and the isomorphisms of actual line bundles lie in universe `u`, even
though the category of line bundles has its objects in universe `u + 1`.
The presheaf therefore uses `uliftFunctor` to give values in `Type (u + 1)`,
exactly as required by `AlgebraicSpace.Presheaf`. The evaluation lemma
records this lift. Restrictions retain the point-fibre construction's
actual coherent pullback maps, after precomposition with
`T.iteratedSliceBackward.op`. Every test scheme and every morphism is
included, with no affine, reduced, quasi-compact or nonempty restriction.

`IsSmoothSurjectivePresentation f L` requires that for every `T` and
every actual `M`, this full presheaf be naturally isomorphic to the lifted
Yoneda presheaf of an actual scheme `P` over `T.left`, and that
`P → T.left` be smooth and surjective. Representation is in that slice,
so this structure morphism is the projection of the represented point
fibre.

`HasSmoothSchemeAtlas f` asserts the existence of such `U` and `L`.
`HasLocallyFiniteTypeSmoothSchemeAtlas f` additionally requires that
`U → S` be locally of finite type. The forgetful lemma retains the same
scheme, line bundle and presented fibres.

These conditions specifically use representation of point fibres by
schemes. No equivalence with a general definition of algebraic stacks
is claimed. The module supplies no descent theorem, no atlas existence
proof, and no Picard-sheaf representability assertion. It applies to the
actual relative line-bundle pseudofunctor without properness, flatness,
field, finiteness, section or global-functions hypotheses.
