# Base change of perfect models and closed restriction

Authors: Worker 727 and Worker 950 (Worker 950 specified the declaration shapes).

Module `Langlands.AlgebraicGeometry.Modules.PerfectModelRestriction`, namespace
`Langlands.AlgebraicGeometry.Modules.DerivedSections`. Take a derived morphism
`a : K ⟶ RΓ_R(X, L)` from a strictly perfect complex of `R`-modules. The module
builds its `T`-linear version over a base change `X' = X ×_{Spec R} Spec T`. It
proves that this construction is compatible with restriction along a closed
immersion. Everything is proved in the file, with no hypotheses beyond those in
the signatures and no proof holes. The module does not assert that any of these
maps is an isomorphism. Isomorphism results for perfect models are geometric
inputs that this module does not provide.

## Conventions

All schemes are in one universe `u`. Write `h_*`, `h^*` for Mathlib's
`Scheme.Modules.pushforward h` and `Scheme.Modules.pullback h`. For
`f : X ⟶ Spec R`, `RΓ_R(X, M)` is
`(DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).obj M`
in the derived category of `R`-modules, as in the Library's `DerivedRestriction`.
`Q` is `DerivedCategory.Q`. `T ⊗_R K` is `(ModuleComplex.baseChange φ.hom).obj K`,
the Library's termwise scalar extension. `Res_φ` is
`(ModuleCat.restrictScalars φ.hom).mapDerivedCategory`. `equiv K` is the Library's
`ModuleComplex.perfectScalarDerivedTargetHomEquiv φ.hom K hK _`, which identifies
maps `Q(T ⊗_R K) ⟶ Y` with maps `Q(K) ⟶ Res_φ Y` for strictly perfect `K`.
`LineBundle X` is the Library's full subcategory of locally free rank-one
modules, with underlying module `L.obj`.

Data: `φ : R ⟶ T`, `f : X ⟶ Spec R`, `f' : X' ⟶ Spec T`, `p : X' ⟶ X` with
`hp : IsPullback p f' f (Spec.map φ)`, and `g : Y ⟶ X`, `q : Y' ⟶ Y`,
`g' : Y' ⟶ X'` with `hq : IsPullback q g' g p`.

## Declarations

- `perfectModelBaseChange hp L hK a` (a `def`): for `L : LineBundle X`, a
  strictly perfect `K` (`hK : ModuleComplex.IsStrictlyPerfect K`) and
  `a : Q(K) ⟶ RΓ_R(X, L)`, the morphism
  `Q(T ⊗_R K) ⟶ RΓ_T(X', p^* L)` defined as
  `(equiv K).symm (a ≫ derivedBaseChangeMapLineBundle hp L)`. Here
  `derivedBaseChangeMapLineBundle hp L : RΓ_R(X, L) ⟶ Res_φ RΓ_T(X', p^* L)` is
  the Library's derived base change map for a line bundle
  (`DerivedRestrictionLineBundle`).
- `perfectScalarDerivedTargetHomEquiv_perfectModelBaseChange`: the defining
  equation `equiv K (perfectModelBaseChange hp L hK a) = a ≫ derivedBaseChangeMapLineBundle hp L`.
- `perfectModelRestrictionBaseChange hp hq L hK' a'` (a `def`): for a closed
  immersion `g`, a strictly perfect `K'` and
  `a' : Q(K') ⟶ RΓ_R(Y, g^* L)` (over `g ≫ f`), the composite

  `perfectModelBaseChange (hq.paste_vert hp) (g^* L) hK' a' ≫ RΓ_T(Y', (pullbackSquareIso p g g' q hq.w).hom_L) ≫ (derivedPushforwardComparisonIso g' f' _ _).hom`,

  a morphism `Q(T ⊗_R K') ⟶ RΓ_T(X', g'_* g'^* p^* L)`. The first factor uses
  the outer pullback square `q ≫ g ≫ f = g' ≫ f' ≫ Spec.map φ` and the line
  bundle `(LineBundle.pullback g).obj L`. The second factor is the
  isomorphism `q^* g^* L ≅ g'^* p^* L`. The third factor is the Library's
  isomorphism `RΓ_T(Y', g'^* p^* L) ≅ RΓ_T(X', g'_* g'^* p^* L)` for the closed
  immersion `g'`. The closed-immersion instance for `g'` is
  `isClosedImmersion_of_isPullback hq`. The vanishing argument is the
  Library's `isZero_higherDirectImage_of_isClosedImmersion`.
- `isIso_perfectModelRestrictionBaseChange_iff`:
  `IsIso (perfectModelRestrictionBaseChange hp hq L hK' a')` holds if and only
  if `IsIso (perfectModelBaseChange (hq.paste_vert hp) (g^* L) hK' a')` does,
  because the other two factors are isomorphisms.
- `perfectModelBaseChange_restriction` (theorem): for a closed immersion `g`,
  strictly perfect `K`, `K'`, a chain map `ψ : K ⟶ K'`,
  `a : Q(K) ⟶ RΓ_R(X, L)` and `a' : Q(K') ⟶ RΓ_R(Y, g^* L)` with
  `h : Q.map ψ ≫ a' = a ≫ derivedRestrictionMap g f L`,

  `Q.map (T ⊗_R ψ) ≫ perfectModelRestrictionBaseChange hp hq L hK' a'`
  `= perfectModelBaseChange hp L hK a ≫ RΓ_T(X', η_{p^* L})`,

  where `η` is the unit of Mathlib's `Scheme.Modules.pullbackPushforwardAdjunction g'`.

## Proof of the restriction theorem

Apply the injective function `equiv K` to both sides. The source naturality
`perfectScalarDerivedTargetHomEquiv_naturality_source` (module
`Langlands.Cohomology.PerfectScalarDerivedTargetSource`) moves `T ⊗_R ψ` out as
`Q.map ψ`. The Library's target naturality
`perfectScalarDerivedTargetHomEquiv_naturality` and the defining equation of
`perfectModelBaseChange` turn the left side into
`Q.map ψ ≫ a' ≫ (base change for the outer square) ≫ Res_φ(...)` and the right
side into `a ≫ derivedBaseChangeMapLineBundle hp L ≫ Res_φ RΓ_T(X', η)`. Then
`h` replaces `Q.map ψ ≫ a'` by `a ≫ derivedRestrictionMap g f L`. By the
Library's definition, `derivedRestrictionMap g' f' (p^* L)` followed by the
comparison isomorphism is `RΓ_T(X', η)`. The Library's
`derivedRestrictionMap_comp_derivedBaseChangeMap_lineBundle_of_isPullback hp hq L`
then identifies the two sides. The definitions involved (the base change maps
for the outer square for `(LineBundle.pullback g).obj L` and for
`(Scheme.Modules.pullback g).obj L.obj`) agree definitionally. The proofs of
the isomorphism criterion and of the theorem therefore use
`backward.isDefEq.respectTransparency false`.

## Provenance

Internal: formal constructions from the Library's derived base change and
restriction maps and its perfect-source scalar adjunction. Worker 950 specified
the declaration shapes for use in a proof that perfect models of line-bundle
cohomology are compatible with restriction along closed immersions. No
literature statement is formalized, and no external mathematical assertion is
used.
