# Intrinsic relative module Hom presheaves

For an arbitrary morphism of schemes `p : Y ⟶ B` and arbitrary sheaves of
modules `M N : Y.Modules`, `intrinsicModuleHomPresheaf p M N` is the
presheaf on the entire slice `Over B` whose value at `Z ⟶ B` is

```text
ULift ((q* M) ⟶ (q* N)),   q : Z ×_B Y ⟶ Y.
```

Here `q` is the second projection of the chosen pullback. The lift has
the explicit value universe used by `AlgebraicSpace.Presheaf B`.
`intrinsicModuleHomPointsEquiv` is the identity equivalence with these
actual module maps. Restrictions use the ordinary module pullback
pseudofunctor, including its composition comparisons.

`intrinsicModulePseudofunctor` composes Mathlib's adjunction-valued
`Scheme.Modules.pseudofunctor` with `Adj.forget₁`. Thus it retains the
ordinary pullback functors and their coherence maps.

Two generic categorical comparisons supply the bookkeeping:

- `precompPresheafHomIso` identifies the Hom presheaf of a reindexed
  Cat-valued pseudofunctor with the Hom presheaf reindexed by `Over.post`.
  Its components are identity maps. Naturality is proved by unfolding
  `pullHom` and the pseudofunctor composition comparison, reducing the
  locally discrete comparison to equality morphisms, and composing
  those equality morphisms.
- `compAssocPresheafHomIso` compares the two associations of three
  composed pseudofunctors. Its components are identities. The naturality
  proof uses functoriality on 2-morphisms and associativity of composition.

Fix `f : X ⟶ S` and `T : Over S`, and put
`Y = (Picard.relativeSpace f).obj T` and
`p = (Picard.relativeProjection f).app T : Y ⟶ T.left`.
`relativeSpaceSlicePullbackIso` identifies the following functors from
`Over T.left` to `Over Y`:

```text
T.iteratedSliceBackward ⋙ Over.post (Picard.relativeSpace f)
Over.pullback p.
```

For each test object `Z`, the component is the canonical pullback
isomorphism from
`Picard.relativeProjection_isPullback f (FamilyGroupoid.testMap T Z)`,
with the square flipped so that the chosen pullback is `Z ×_T Y`.
Its compatibility with the map to `Y` follows from the second projection
identity. Naturality follows by checking the two pullback projections:
the first is naturality of `relativeProjection`, and the second is
functoriality of `relativeSpace` with the slice commutativity equation.

`modulePseudofunctorHomIso` specializes the composition-association
comparison to the published relative-space module pseudofunctor.
`moduleHomPresheafIntrinsicIso` composes that comparison with
`precompPresheafHomIso`, applies the explicit universe lift, and reindexes
along the opposite of `relativeSpaceSlicePullbackIso`.

Finally, `FamilyGroupoid.homPresheafIntrinsicIso` composes the preceding
isomorphism with `FamilyGroupoid.homPresheafModuleIso`. For every two
actual coherent-family objects over `T`, it identifies their published
Hom presheaf with the intrinsic Hom presheaf of their underlying modules
and the fixed map `p`. This is a natural isomorphism on the whole slice,
retaining all module morphisms and the original ordinary-pullback
restrictions. Its construction requires no additional geometric
hypotheses on `f`, `T`, or the test schemes.

This is derived internal categorical content, using the published
`HomPresheaf`, `Pullback`, and `RelativeSpaceCartesian` constructions and
Mathlib's pseudofunctor Hom presheaf. It prepares the input to a geometric
Hom-representability proof; it supplies no representability or finiteness
claim. The supporting `ModuleHomPresheaf` pair is reused unchanged from
Worker 153's independently submitted draft, with authorship retained.
