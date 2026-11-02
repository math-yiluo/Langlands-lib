# Point fibres and product-base Hom presheaves

This internal construction applies to a category `C`, objects `U, T` with a
binary product, and a contravariant pseudofunctor `F` into categories whose
fibres are groupoids. Fix objects `ξ` over `U` and `η` over `T`.
The construction uses Mathlib's binary products, slice categories, and
pseudofunctor composition isomorphisms. It is derived categorical
infrastructure, with no external geometric existence theorem as an input.

`productOver U T` is the actual second projection `U × T → T`, regarded as
an object of `Over T`. For every `Z : Over T`, `mapsToProductEquiv Z`
identifies a map `a : Z.left → U` with the slice map to this product whose
underlying map is `prod.lift a Z.hom`. Its inverse composes with the first
projection. The two inverse identities follow from the product equations
and the slice commutative triangle.

`productHom F ξ η` is the full-slice Hom presheaf of the pullbacks of `ξ`
and `η` along the first and second projections. `compIso` is the supplied
pseudofunctor's comparison between pullback along a composite and the
iterated pullback. `pointsEquiv` combines the product-map equivalence,
the equivalence between isomorphisms and arrows in a groupoid, and these
composition comparisons. Its domain is the actual point fibre: a map
`a : Z.left → U` together with an isomorphism from `a*ξ` to `Z.hom*η`.
Its codomain is the dependent sum retaining the product slice map and
an actual section of `productHom` at that map.

`pointsEquiv_restrict` proves naturality for every morphism `Z' → Z`
in `Over T`. The first components agree by the product equations.
After aligning those components, the second components agree by the
two pseudofunctor composition-coherence identities used also for
restriction of Hom presheaves. `presheafIso` packages this as a natural
isomorphism

`PseudofunctorPointFiber.presheaf F ξ η ≅
 SlicePresheafTotal.total (productOver U T) (productHom F ξ η)`.

The object universe, base morphism universe, and fibre object and morphism
universes are independent. Both presheaves take values in the maximum
of the base and fibre morphism universes. All test objects and slice
restriction maps occur in this comparison.

This unit identifies two explicit presheaves. It does not assert that
the Hom presheaf or point fibre has a representing scheme, and establishes
no smoothness, local finite presentation, surjectivity, or atlas existence.
