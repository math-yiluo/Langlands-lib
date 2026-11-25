# Torsion-closed immersions: transport and fppf descent

This module is an internal helper for the proof of
`Langlands.GroupScheme.MultiplicativeTypeTorsionDeterminationStatement` (SGA 3 IX,
Corollaires 4.8 and 4.9). It introduces no statement of its own from the literature. It
defines the notion of a *torsion-closed* morphism into a group scheme, which is the
hypothesis of the lemma that the whole proof rests on (every torsion-closed immersion into a
group of multiplicative type is an isomorphism, see
[`Assembly`](Assembly.md) and [`Reduction`](Reduction.md)), and shows that this notion and
the conclusion "the identity point lifts" behave well under pullback along homomorphisms,
base change, and fppf descent. All declarations are in the namespace
`Langlands.GroupScheme.TorsionDetermination`.

Throughout, `S` is a scheme, `GroupScheme S = Grp (Over S)`, and for an object `X` of
`Over S` the points `T ⟶ X` over `S`-schemes `T` form a group when `X` is the underlying
object of a group scheme (scoped notation of `CategoryTheory.MonObj`).

## Definitions

- `PointLifts j x`, for a morphism of schemes `j : Z ⟶ X.left` and a point `x : T ⟶ X` over
  `S`: there is a morphism of schemes `a : T.left ⟶ Z` with `a ≫ j = x.left`. No
  structure of `S`-scheme on `Z` is needed.
- `IsTorsionClosed G j`, for `G : GroupScheme S` and `j : Z ⟶ G.X.left`, is a structure
  with two fields:
  - `mul`: for every `S`-scheme `T` and points `x y : T ⟶ G.X`, if `x` and `y` lift through
    `j`, so does `x * y`;
  - `torsion`: for every `n > 0`, every `S`-scheme `T` and every `x : T ⟶ G.X` with
    `x ^ n = 1`, the point `x` lifts through `j`.

  So the points lifting through `j` form a multiplicatively closed set containing all
  torsion points (closure under inverses is not required and not used). For a subgroup
  `h : H ⟶ G` containing every `ₙG`, the underlying morphism `h.hom.hom.left` is
  torsion-closed (`isTorsionClosed_of_range` in [`Assembly`](Assembly.md)).

## Results

- `PointLifts.comp`: lifting is stable under precomposition with a morphism `T' ⟶ T` over `S`.
- `isIso_of_lifts_id`: if `j` is a monomorphism and the identity point `𝟙 X` lifts through
  `j`, then `j` is an isomorphism (`j` is then a split epimorphism and a monomorphism).
  `lifts_id_of_isIso` is the converse direction for an isomorphism `j`.
- `IsTorsionClosed.one` (the unit point lifts, being `1`-torsion) and `IsTorsionClosed.prod`
  (a finite product of lifting points lifts, for a commutative `G`), proved by induction on
  the finset.
- **Pullback along a homomorphism.** For `φ : G' ⟶ G` and `j : Z ⟶ G.X.left`,
  `lifts_pullback_iff` says that a point `y` of `G'` lifts through
  `pullback.snd j φ.hom.hom.left` exactly when `y ≫ φ.hom.hom` lifts through `j` (by the
  universal property of the pullback). Since `φ` is a homomorphism, composition with
  `φ.hom.hom` preserves products, powers and the unit (`MonObj.mul_comp`,
  `MonObj.pow_comp`, `MonObj.one_comp`), which gives `IsTorsionClosed.pullback`.
  `lifts_id_of_pullback_iso`: for an isomorphism `e : G' ≅ G`, if the identity point of
  `G'` lifts through the pullback of `j` along `e.hom`, then the identity point of `G`
  lifts through `j` (compose with `e.inv`).
- **Base change.** For `b : S' ⟶ S`, `baseChangeι b G j` is the base change
  `pullback.snd j (pullback.fst G.X.hom b)` of `j`, a morphism into the underlying scheme of
  `(GroupScheme.baseChange b).obj G`. The published group isomorphism
  `baseChangePointsEquiv` (from `Langlands.AbelianScheme.KernelBaseChange`) between
  `T`-points of the base change and `T`-points of `G` over `S`, whose underlying morphism is
  the composite with the first projection (`baseChangePointsEquiv_left`), gives
  `lifts_baseChange_iff` and hence `IsTorsionClosed.baseChange`. `lifts_baseChange_id_iff`
  rewrites lifting of the identity point of the base change as the existence of
  `a : pullback G.X.hom b ⟶ Z` with `a ≫ j = pullback.fst G.X.hom b`.
- **fppf descent.** `effectiveEpiFamily_of_fppf`: every cover of a scheme in the fppf
  precoverage (`Flat ⊓ LocallyOfFinitePresentation`) is an effective epimorphic family. This
  is Mathlib's subcanonicity of the fppf topology (`Scheme.fppfTopology`, representable
  presheaves are sheaves) translated through
  `Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda`.
  `lifts_id_of_cover`: let `j` be a monomorphism and `𝒰` an fppf cover of `S`; if for every
  member `𝒰.f i` the identity point of the base change of `G` lifts through
  `baseChangeι (𝒰.f i) G j`, then the identity point of `G` lifts through `j`. Proof: the
  lifts `a i : pullback G.X.hom (𝒰.f i) ⟶ Z` agree on overlaps because `j` is a
  monomorphism, and the pulled-back cover `𝒰.pullback₁ G.X.hom` of `G.X.left` is an
  effective epimorphic family, so they glue (`EffectiveEpiFamily.desc`) to a lift of the
  identity point.

## Provenance

These are standard categorical facts used to carry out the reduction to diagonalizable
groups. SGA 3 makes the same kind of reduction by faithfully flat descent in the proof of
Théorème 4.7 (p.47 of the Gille–Polo edition, registered as `sga3-expose-ix-gille-polo-2009`);
here it is applied to the lifting property directly rather than to schematic density. The notion `IsTorsionClosed` is
internal to this proof: it isolates exactly the properties of a subgroup containing all
torsion that the core argument uses.
