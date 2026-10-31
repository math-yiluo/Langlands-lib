# Restriction and affine base change for line bundles

Author: Worker 727.

Module `Langlands.AlgebraicGeometry.Modules.DerivedRestrictionLineBundle`,
namespace `Langlands.AlgebraicGeometry.Modules.DerivedSections`. It proves:

1. Along an affine morphism, the higher direct images of the pullback of a
   locally free rank-one module vanish.
2. Consequently, for line bundles and affine base change morphisms, the
   Library's compatibility of derived restriction along closed immersions with
   derived base change holds with no vanishing hypotheses.
3. The same compatibility, stated for the shape of two stacked pullback
   squares over `Spec.map φ`, for a line bundle `L` on `X`. The module also
   defines `derivedBaseChangeMapLineBundle`, the derived base change map of `L`
   along such a square with its vanishing hypothesis discharged.

Everything is proved in the file, with no hypotheses beyond those in the
signatures and no proof holes.

## Conventions

All schemes are in one universe `u`. Write `h_*`, `h^*` for Mathlib's
`Scheme.Modules.pushforward h`, `Scheme.Modules.pullback h`, and
`R^{q+1} h_*` for the Library's `higherDirectImage h (q + 1)`.
`IsLocallyFreeRankOne M` and `LineBundle X` (the full subcategory of locally
free rank-one modules, with underlying module `L.obj` and proof `L.property`)
are the Library's, from `Langlands.AlgebraicGeometry.Picard.LineBundle`.

## Section `Vanishing`

- `isZero_higherDirectImage_pullback_of_isLocallyFreeRankOne g hM q`: for an
  affine morphism `g : X' ⟶ X` (`[IsAffineHom g]`) and a locally free rank-one
  `M` on `X`, `R^{q+1} g_*(g^* M) = 0`. Proof: `g^* M` is quasi-coherent by the
  Library's `IsLocallyFreeRankOne.isQuasicoherent_pullback`, and the Library's
  `affineQuasicoherentHigherDirectImageVanishing` gives the vanishing.

## Section `BaseChange`

Data: `φ : R ⟶ R'`, `f : X ⟶ Spec R`, `f' : X' ⟶ Spec R'`, an affine
`g : X' ⟶ X` with `w : g ≫ f = f' ≫ Spec.map φ`, closed immersions
`i : Z ⟶ X` and `i' : Z' ⟶ X'`, an affine `gZ : Z' ⟶ Z` with
`sq : gZ ≫ i = i' ≫ g`, and `hM : IsLocallyFreeRankOne M` for `M : X.Modules`.

- `derivedRestrictionMap_comp_derivedBaseChangeMap_of_isLocallyFreeRankOne`:
  the equality of `derivedRestrictionMap_comp_derivedBaseChangeMap_of_vanishing`
  (module `DerivedRestrictionVanishing`). The two base change maps use the
  vanishing proofs of the previous section, for `g` and `M` and for `gZ` and
  `i^* M`. The latter is locally free of rank one by the Library's
  `IsLocallyFreeRankOne.pullback`.
- `restrictionCohomologyMap_comp_baseChangeMap_of_isLocallyFreeRankOne`: the
  degreewise form, from `restrictionCohomologyMap_comp_baseChangeMap_of_vanishing`.
  The injective-acyclicity arguments of `baseChangeMap` are the Library's
  `pushforwardInjectiveAcyclic`, as in the published theorems.

## Section `IsPullback`

Data: `φ : R ⟶ T`, `f : X ⟶ Spec R`, `f' : X' ⟶ Spec T`, `p : X' ⟶ X` with
`hp : IsPullback p f' f (Spec.map φ)`, and `g : Y ⟶ X`, `q : Y' ⟶ Y`,
`g' : Y' ⟶ X'` with `hq : IsPullback q g' g p`. So `X' = X ×_{Spec R} Spec T`
and `Y' = Y ×_X X'`.

- `isAffineHom_of_isPullback_spec hp`: `p` is affine, as a base change of the
  affine morphism `Spec.map φ` (Mathlib's `MorphismProperty.of_isPullback`).
- `isAffineHom_of_isPullback_isPullback_spec hp hq`: `q` is affine, as a base
  change of `p`.
- `isClosedImmersion_of_isPullback hq`: if `g` is a closed immersion, so is `g'`.
- `isZero_higherDirectImage_pullback_lineBundle_of_isPullback hp L n`:
  `R^{n+1} p_*(p^* L) = 0` for `L : LineBundle X`.
- `isZero_higherDirectImage_pullback_pullback_lineBundle_of_isPullback hp hq L n`:
  `R^{n+1} q_*(q^* g^* L) = 0`.
- `derivedBaseChangeMapLineBundle hp L` (an `abbrev`): the Library's
  `derivedBaseChangeMap φ f f' p hp.w L` with its vanishing hypothesis supplied
  by the previous lemma, a morphism
  `RΓ_f(L) ⟶ Res_φ RΓ_{f'}(p^* L)` in the derived category of `R`-modules. It
  is reducible, so it unfolds to that map.
- `derivedRestrictionMap_comp_derivedBaseChangeMap_lineBundle_of_isPullback hp hq L`,
  for a closed immersion `g`: with the closed-immersion instance for `g'` from
  `isClosedImmersion_of_isPullback hq`,

  `derivedRestrictionMap g f L ≫ derivedBaseChangeMap φ (g ≫ f) (g' ≫ f') q _ (g^* L) _ ≫ Res_φ(RΓ_{g' ≫ f'}(pullbackSquareIso p g g' q hq.w).hom_L)`
  `= derivedBaseChangeMapLineBundle hp L ≫ Res_φ(derivedRestrictionMap g' f' (p^* L))`.

  Here `Res_φ` is `(ModuleCat.restrictScalars φ.hom).mapDerivedCategory` and
  `RΓ_{g' ≫ f'}` is the derived complex of `relativeGlobalSections (g' ≫ f')`,
  as in `DerivedRestriction`. The commuting square for the restricted base
  change is the Library's `square_restrict_comm φ f f' p hp.w g g' q hq.w`. The
  vanishing arguments are the two lemmas above. Proof: the instances above
  and `derivedRestrictionMap_comp_derivedBaseChangeMap_of_isLocallyFreeRankOne`.
- `restrictionCohomologyMap_comp_baseChangeMap_lineBundle_of_isPullback hp hq L n`:
  the degreewise form, from
  `restrictionCohomologyMap_comp_baseChangeMap_of_isLocallyFreeRankOne`.

## Provenance

Internal: these are deductions about the Library's own derived restriction
and base change maps. They combine the published vanishing of higher direct
images of quasi-coherent modules along affine morphisms, quasi-coherence of
pulled-back line bundles, and stability of affine morphisms and closed
immersions under base change (Mathlib). No literature statement is
formalized, and no external mathematical assertion is used.
