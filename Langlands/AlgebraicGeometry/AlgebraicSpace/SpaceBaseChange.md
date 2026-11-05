# Base change of algebraic spaces

Author: Worker 105.

This module constructs the base change of an actual algebraic space along a morphism
of base schemes, in the Library's conventions of
`Langlands/AlgebraicGeometry/AlgebraicSpace/Basic.lean`. An algebraic space over
`S` is an fppf sheaf on `Over S` with values in `Type (u + 1)`. Its diagonal is
representable by actual schemes, and it has a surjective étale scheme atlas.

## Source

The construction is the base change of the Stacks Project. The registered source is
`stacks-algebraic-spaces-chapter-ed88ff78-2026-11-05` (chapter Algebraic Spaces,
version ed88ff78; registered folder fingerprint
`49a75fa582cbeafadb9e1fbbdce130e5b8971322a2c0048d777e8a97f0d0fcf5`). Let
`g : S → S'` be a morphism and `j` the localization functor. Lemma 16.1 (Tag 03I4)
says: "(4) for a scheme `T` over `S` we have `j^{-1}F'(T/S) = F'(T/S')`", "(5) if
`F'` is representable by a scheme `X'` …, then `j^{-1}F'` is representable, namely by
`X'_S = S ×_{S'} X'`", and "(6) if `F'` is an algebraic space, then `j^{-1}F'` is an
algebraic space". Definition 16.2 (Tag 03I5) calls `j^{-1}F'` the base change `F'_S`.

Conrad's paper (registered source `conrad-2011-weil-grothendieck-adelic-points`)
uses such base changes throughout Section 5. Examples are `X(k̂) = X_k̂(k̂)` in
Proposition 5.11 (printed p.18) and the local factors `X_v` of a model over
`O_{F,S}`.

## Construction

Fix `g : T ⟶ S` (the roles of `S` and `S'` above are played by `T` and `S`).

- `restrictPresheaf g : Presheaf S ⥤ Presheaf T` is precomposition with
  `(Over.map g).op`. A scheme `Z` over `T` is viewed over `S` through `g`, so
  `((restrictPresheaf g).obj F).obj (op Z) = F.obj (op ((Over.map g).obj Z))`. This
  is formula (4).
- `relative_restrictPresheaf_map`: let `P` be a property of scheme morphisms that
  respects isomorphisms. If every base change of `f : F ⟶ G` along a scheme over `S`
  is represented by a scheme morphism with `P`, then the same holds for the
  restriction of `f`, over `T`. For a scheme `U` over `T` and a map `α` from it to the
  restriction of `G`, view `U` over `S` and take the represented pullback `V ⟶ U`
  over `S`. The scheme `V` with structure map `V ⟶ U ⟶ T` represents the pullback
  over `T`, with the same underlying scheme morphism. The pullback property is
  checked on every test scheme `Z` over `T`: morphisms `Z ⟶ V` over `T` and
  morphisms `Z ⟶ V` over `S` that lie over `U` correspond. This is checked with
  Mathlib's criterion `Types.isPullback_iff` and `IsPullback.of_forall_isPullback_app`.
  `relativelyRepresentable_restrictPresheaf_map` is the case of representability
  alone.
- `restrictPresheafProdIso` and `restrictPresheaf_map_diag`: restriction preserves
  binary products, and it carries the diagonal of `F` to the diagonal of the
  restriction (Mathlib's `PreservesLimitPair.iso` for precomposition functors).
  Hence `relative_diag_restrictPresheaf` and
  `hasRepresentableDiagonal_restrictPresheaf` transfer any such relative property of
  the diagonal, and its representability.
- `restrictAtlas g a` is the restriction of a scheme atlas `a`, precomposed with the
  published `schemeYonedaBaseChangeIso g U` (from `SchemeBaseChange.lean`). That
  isomorphism identifies the restriction of the functor of points of `U` with the
  functor of points of the actual base change `(Over.pullback g).obj U = U ×_S T`.
  This is formula (5). `relative_restrictAtlas` transfers étaleness and surjectivity
  to it.
- `isAlgebraicSpace_restrict` proves that the restricted sheaf is an algebraic space
  over `T`, which is part (6). The sheaf is Mathlib's
  `Scheme.fppfTopology.overMapPullback (Type (u + 1)) g`, the pushforward of fppf
  sheaves along the continuous functor `Over.map g`. Its underlying presheaf is
  `(restrictPresheaf g).obj X.presheaf` (`baseChange_presheaf`, by `rfl`).
- `baseChange g X : AlgebraicSpace T` is this algebraic space, the base change
  `X_T` of Definition 16.2. `baseChangeMap g f` restricts a morphism, and
  `baseChangeFunctor g` packages these as a functor.
- `baseChangeSchemeIso g U` is the isomorphism of algebraic spaces over `T` between
  the space of the actual scheme `U ×_S T` and the base change of the space of `U`.
- `IsQuasiSeparated.baseChange` and `IsSeparated.baseChange`: base change keeps the
  quasi-separatedness and separatedness of `RingPoints.lean`.
  `HasAtlasProperty.baseChange`: for a property `P` of scheme morphisms stable under
  base change, an atlas with structure morphism in `P` gives one for the base change.
  In particular local finite type over the base (`LocallyOfFiniteTypeOverBase`) is
  kept.

## Points

Let `C → D` be a ring map and `A` a `D`-algebra whose `C`-algebra structure is the
composite (`IsScalarTower C D A`). `baseChangeRingPointsEquiv C D A X` identifies
the `A`-valued points of the base change of `X` along `Spec D ⟶ Spec C` with the
`A`-valued points of `X` over `C`. It is pullback along the published
`ringTestRestrictScalarsIso C D A`, which identifies `Spec A` over `Spec D`, viewed
over `Spec C`, with `Spec A` over `Spec C` (`baseChangeRingPointsEquiv_apply`).
`baseChangeRingPointsEquiv_map` proves naturality in morphisms of algebraic spaces.
This is formula (4) for the test schemes `Spec A`.

## Provenance

Part (6) is the Stacks result. The proof here is the Library's own: it uses the
Library's representability conventions directly instead of presentations by étale
equivalence relations. The names, the transfer lemmas, the scheme comparison and the
point identification are internal API for the Section 5 statements of Conrad's
paper.
