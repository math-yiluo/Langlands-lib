# Ordinary pullback of flat finitely presented families

Fix arbitrary schemes `X S : Scheme.{u}` and `f : X ⟶ S`. This module constructs
`FamilyGroupoid.pseudofunctor f : LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat` in the
namespace `Langlands.AlgebraicGeometry.CoherentSheaves`. It has the actual
flat finitely presented module-family groupoid at every test scheme, and
ordinary module pullback along every map of test schemes. The universe `u`
and the full slice `Over S` are retained.

The imported `FamilyGroupoid f T` is the core of the full family category on
`(Picard.relativeSpace f).obj T = T.left ×_S X`, with structure morphism
`(Picard.relativeProjection f).app T`. A family is an actual module sheaf
with Mathlib's local finite free presentation condition and the published
`Modules.IsFlatOver` condition through the actual projection's stalk maps.
Local finite presentation implies quasi-coherence. The core keeps all
actual module isomorphisms as arrows.

`modulePseudofunctor f` composes the actual relative-space functor with the
published `Scheme.Modules.pseudofunctor`, then forgets adjunction data using
`Adj.forget₁`. Its functor at `h : U ⟶ T` is precisely
`Scheme.Modules.pullback ((Picard.relativeSpace f).map h)`. Its comparisons
therefore include both the published ordinary module-pullback comparisons
and the equality transports from relative-space functoriality.

`familyProperty f` is the family predicate in these module categories. Its
closure under pullback has an intrinsic proof: the published
`Modules.isFinitePresentation_pullback` preserves local finite presentation,
and `Modules.isFlatOver_pullback_of_isPullback` preserves relative stalk
flatness in the actual cartesian square supplied by
`Picard.relativeProjection_isPullback`. Its isomorphism closure uses the
already proved isomorphism invariance of the family predicate. Thus
`Family.pseudofunctor f` is Mathlib's induced full-subcategory pseudofunctor.
Its comparisons and coherence are inherited from `modulePseudofunctor f`.

`Family.pullback f h` is its actual restriction functor.
`Family.pullbackForgetIso f h` is the identity natural isomorphism between
forgetting this functor and the ordinary module-pullback composite; this
identifies both objects and module morphisms. `Family.pullbackId` and
`Family.pullbackComp` display its identity and composition comparisons, with
composition oriented from iterated pullback to pullback of the composite.

To pass to groupoids, private general helpers first translate the three
coherence laws of any locally discrete, category-valued pseudofunctor into
ordinary natural-transformation equations. The core construction is also
reused by [Picard/CoherentFamilyComparison](../Picard/CoherentFamilyComparison.md). They use the existing
`map₂_associator`, `map₂_left_unitor` and `map₂_right_unitor` laws and identify
the image of an equality 2-morphism with an equality natural transformation.
The shared `corePseudofunctor` uses the cores of the categories and functors,
and the cores of their comparison natural isomorphisms. Its associativity
and two unit laws follow by extensionality on natural-transformation
components and core morphisms, applying the three translated equations to
the underlying objects. An equality morphism in a core forgets to the
equality morphism of the underlying objects. These are general internal
categorical lemmas; their specialization supplies all coherence fields of
`FamilyGroupoid.pseudofunctor f`.

`FamilyGroupoid.pullback f h` is the core of `Family.pullback f h`.
`pullbackForgetIso` is again an identity natural isomorphism to ordinary
module pullback. `pullback_obj` identifies the underlying pulled-back module,
and `pullback_homEquiv` proves that the action on every actual module
isomorphism is ordinary pullback of that isomorphism. The displayed
`pullbackId` and `pullbackComp` are the pseudofunctor's comparison natural
isomorphisms, with the same composition orientation as for families.
The equations `pseudofunctor_obj`, `pseudofunctor_map`,
`pseudofunctor_mapId` and `pseudofunctor_mapComp` identify this concrete
interface with the packaged pseudofunctor and its coherent comparisons.

For proper `f`, every object in every target groupoid, including each
pulled-back family, has proper scheme-theoretic support by the imported
`FamilyGroupoid.hasProperSupport`. That theorem derives finite affine
sections from local finite presentation and applies the published
annihilator-support construction: its support immersion is closed and the
relative projection is a base change of the proper ambient map.
`FamilyGroupoid.properSupportExists` exhibits the actual closed immersion,
with its affine annihilator-kernel characterization and proper composite.
Consequently support is justified formally after every base change without
adding a support witness to the object fields. The present construction
requires no assumptions on `f`; properness supplies this support conclusion.
In particular it supplies the proper, flat, locally finitely presented
specialization, on empty, nonreduced, nonnoetherian and non-quasi-compact test
schemes as well.

The original source is Stacks Project Section 99.5, registered as
`stacks-coherent-sheaf-stack-08ka-2026-11-01`, folder SHA-256
`4ac7cc2a6a797cd51c3a793bbf7684229a8f43b69031e852a0681c219ab99078`.
In `08KA.html`, Situation 99.5.1 (08KB) specifies the objects and actual
pullback isomorphisms; Lemma 99.5.2 (08W5) and its proof construct ordinary
pullback and use its composition comparisons. The implementation specializes
the algebraic spaces there to schemes and fixes the source's base as `S`.
The source's morphism over `h` is an isomorphism from the pulled-back target
family to the source family, as recovered from this contravariant
pseudofunctor. On a fixed fibre, its inverse identifies that convention with
the forward core arrows used here. The source's proper-support condition is
scheme-theoretic, as made explicit in the proof of Lemma 99.5.4; the imported
support pair establishes that correspondence. The pseudofunctor and core
packaging are internal categorical realizations of this source construction.
This module makes no descent, algebraicity, diagonal, atlas or Picard
representability claim.
