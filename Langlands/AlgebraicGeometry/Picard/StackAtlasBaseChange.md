# Base change of smooth scheme atlases of the actual Picard stack

Namespace: `Langlands.AlgebraicGeometry.Picard.PicardGroupoid`.

This module proves that the published notion
`HasLocallyFiniteTypeSmoothSchemeAtlas` (module `Picard.StackAtlas`) is stable
under base change of the proper scheme. It is internal infrastructure for the
field Picard stack atlas task. It formalizes the standard fact that the
Picard stack of a base change is the base change of the Picard stack, at the
level of the published actual point-fibre presheaves. No new literature
assertion is introduced.

## Setting

Fix schemes `S, S', X, X'`, morphisms `f : X ⟶ S`, `g : X' ⟶ S'`,
`π : X' ⟶ X`, `s : S' ⟶ S`, and an actual Cartesian square
`hπ : IsPullback π g f s`.

## Comparison of relative spaces and Picard pseudofunctors

- `baseChangeRelativeSpaceIso hπ : relativeSpace g ≅ Over.map s ⋙ relativeSpace f`.
  Its component at `T : Over S'` is the canonical isomorphism
  `T ×_{S'} X' ≅ T ×_S X` obtained by pasting the pullback square of `T` and
  `g` with `hπ` (Mathlib's `IsPullback.paste_horiz` and `isoPullback`).
  Naturality is checked on both pullback projections.
- `baseChangeStrongTrans hπ` is the strong transformation
  `relative g ⟶ reindex (Over.map s) (relative f)` given by
  `PseudofunctorReindexIso.strongTrans` for the published line-bundle
  pseudofunctor `PicardGroupoid.pseudofunctor`. Its component at `T` pulls an
  actual line bundle back along the inverse of the comparison isomorphism.
  Every component is fully faithful.
- `iteratedSlicePostMapIso s T` identifies
  `T.iteratedSliceBackward ⋙ Over.post (Over.map s)` with
  `((Over.map s).obj T).iteratedSliceBackward`. Both functors start at
  `Over T.left`; their values differ only by reassociation of a composite.

## The base-changed atlas and test bundles

Let `U₀ : Over S` and `L₀` an actual line bundle on `U₀ ×_S X`.

- `baseChangeCounitBundle L₀` pulls `L₀` back along the counit of
  `Over.map s ⊣ Over.pullback s` (Mathlib's `Over.mapPullbackAdj`).
- `baseChangeAtlasBundle hπ L₀` is the line bundle on
  `((Over.pullback s).obj U₀) ×_{S'} X'` obtained from it by pulling back along
  the comparison isomorphism (the inverse functor of
  `PseudofunctorReindexIso.mapIsoEquivalence`).
- For a test `T : Over S'` and an actual line bundle `M` on `T ×_{S'} X'`,
  `baseChangeTestBundle hπ M` is its transport to `T ×_S X`, i.e. its image
  under the component of `baseChangeStrongTrans hπ` at `T`.

## Point fibres

`baseChangePresheafIso` composes three natural isomorphisms of full
point-fibre presheaves on `Over T`:

1. `PseudofunctorPointFiberTransport.presheafIso` for the fully faithful
   strong transformation `baseChangeStrongTrans hπ`;
2. `PseudofunctorPointFiberObjectIso.presheafIso` for the counit isomorphism of
   the equivalence `mapIsoEquivalence`, which replaces the transported atlas
   bundle by `baseChangeCounitBundle L₀`;
3. `PseudofunctorPointFiberReindex.adjPresheafIso` for the adjunction
   `Over.map s ⊣ Over.pullback s`.

The result is an isomorphism with `(Over.post (Over.map s)).op ⋙` the actual
point-fibre presheaf of `f` at `L₀` and the transported test bundle.
`baseChangePointFiberIso` whiskers it with `T.iteratedSliceBackward.op`,
uses `iteratedSlicePostMapIso`, and lifts universes. This gives an isomorphism
of the published presheaves on the full slice `Over T.left`:

`pointFiberPresheaf g (baseChangeAtlasBundle hπ L₀) M ≅
pointFiberPresheaf f L₀ (baseChangeTestBundle hπ M)`.

## Main theorem

`hasLocallyFiniteTypeSmoothSchemeAtlas_of_isPullback hπ` turns an atlas
`⟨U₀, L₀⟩` of `f` into the atlas `⟨(Over.pullback s).obj U₀,
baseChangeAtlasBundle hπ L₀⟩` of `g`. Local finite type of
`pullback.snd U₀.hom s` is Mathlib's base-change stability. For every test
`T` and `M`, the hypothesis applied at `(Over.map s).obj T` (whose underlying
scheme is `T.left`) and `baseChangeTestBundle hπ M` gives a scheme
`P : Over T.left` with smooth surjective structure map. Its Yoneda presheaf
is identified with the point fibre of `g` by composing with
`baseChangePointFiberIso`. The same representing scheme `P` and the same
properties are used.

All test schemes, actual line bundles and actual isomorphisms are retained.
No hypothesis on the schemes beyond the Cartesian square is used.
