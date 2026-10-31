import Langlands.AlgebraicGeometry.Modules.DerivedRestrictionVanishing
import Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentHigherDirectImageVanishingProof
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent

/-!
# Restriction and affine base change for line bundles

Higher direct images of the pullback of a locally free rank-one module along an affine morphism
vanish. Hence the compatibility of derived restriction along closed immersions with derived base
change holds for line bundles without vanishing hypotheses when both base change morphisms are
affine. This applies in particular to a base change `p` of `Spec.map φ` and to the base change
of `p` along a closed immersion.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

attribute [local instance] HasDerivedCategory.standard

section Vanishing

variable {X X' : Scheme.{u}} (g : X' ⟶ X) [IsAffineHom g]

/-- Higher direct images of the pullback of a locally free rank-one module along an affine
morphism vanish in every positive degree. -/
theorem isZero_higherDirectImage_pullback_of_isLocallyFreeRankOne {M : X.Modules}
    (hM : IsLocallyFreeRankOne M) (q : ℕ) :
    IsZero ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pullback g).obj M)) :=
  affineQuasicoherentHigherDirectImageVanishing X' X g inferInstance _
    (hM.isQuasicoherent_pullback g) q

end Vanishing

section BaseChange

variable {X X' Z Z' : Scheme.{u}} {R R' : CommRingCat.{u}} (φ : R ⟶ R') (f : X ⟶ Spec R)
  (f' : X' ⟶ Spec R') (g : X' ⟶ X) [IsAffineHom g] (w : g ≫ f = f' ≫ Spec.map φ)
  (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ X') [IsClosedImmersion i'] (gZ : Z' ⟶ Z)
  [IsAffineHom gZ] (sq : gZ ≫ i = i' ≫ g) {M : X.Modules} (hM : IsLocallyFreeRankOne M)

/-- For a locally free rank-one module and affine base change morphisms, derived restriction
along closed immersions commutes with derived base change. -/
theorem derivedRestrictionMap_comp_derivedBaseChangeMap_of_isLocallyFreeRankOne :
    derivedRestrictionMap i f M ≫
        derivedBaseChangeMap φ (i ≫ f) (i' ≫ f') gZ (square_restrict_comm φ f f' g w i i' gZ sq)
          ((Scheme.Modules.pullback i).obj M)
          (isZero_higherDirectImage_pullback_of_isLocallyFreeRankOne gZ (hM.pullback i)) ≫
        (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
          ((DerivedPlus.derivedComplex (relativeGlobalSections (i' ≫ f')) ⋙
            DerivedCategory.Plus.ι).map ((pullbackSquareIso g i i' gZ sq).hom.app M)) =
      derivedBaseChangeMap φ f f' g w M
          (isZero_higherDirectImage_pullback_of_isLocallyFreeRankOne g hM) ≫
        (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
          (derivedRestrictionMap i' f' ((Scheme.Modules.pullback g).obj M)) :=
  derivedRestrictionMap_comp_derivedBaseChangeMap_of_vanishing φ f f' g w i i' gZ sq M _ _

/-- Degreewise form of `derivedRestrictionMap_comp_derivedBaseChangeMap_of_isLocallyFreeRankOne`.
-/
theorem restrictionCohomologyMap_comp_baseChangeMap_of_isLocallyFreeRankOne (n : ℕ) :
    restrictionCohomologyMap i f M n ≫
        baseChangeMap φ (i ≫ f) (i' ≫ f') gZ (square_restrict_comm φ f f' g w i i' gZ sq)
          ((Scheme.Modules.pullback i).obj M)
          (isZero_higherDirectImage_pullback_of_isLocallyFreeRankOne gZ (hM.pullback i))
          (fun J hJ q => (pushforwardInjectiveAcyclic Z' Z gZ J hJ q).2 R (i ≫ f)) n ≫
        (ModuleCat.restrictScalars φ.hom).map ((relativeCohomology (i' ≫ f') n).map
          ((pullbackSquareIso g i i' gZ sq).hom.app M)) =
      baseChangeMap φ f f' g w M (isZero_higherDirectImage_pullback_of_isLocallyFreeRankOne g hM)
          (fun J hJ q => (pushforwardInjectiveAcyclic X' X g J hJ q).2 R f) n ≫
        (ModuleCat.restrictScalars φ.hom).map
          (restrictionCohomologyMap i' f' ((Scheme.Modules.pullback g).obj M) n) :=
  restrictionCohomologyMap_comp_baseChangeMap_of_vanishing φ f f' g w i i' gZ sq M _ _ n

end BaseChange

section IsPullback

variable {X X' Y Y' : Scheme.{u}} {R T : CommRingCat.{u}} {φ : R ⟶ T} {f : X ⟶ Spec R}
  {f' : X' ⟶ Spec T} {p : X' ⟶ X} (hp : IsPullback p f' f (Spec.map φ))
  {g : Y ⟶ X} {q : Y' ⟶ Y} {g' : Y' ⟶ X'} (hq : IsPullback q g' g p)

include hp in
/-- A base change of `Spec.map φ` is affine. -/
lemma isAffineHom_of_isPullback_spec : IsAffineHom p :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) hp.flip inferInstance

include hp hq in
/-- The base change of a base change of `Spec.map φ` along any morphism is affine. -/
lemma isAffineHom_of_isPullback_isPullback_spec : IsAffineHom q :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) hq.flip (isAffineHom_of_isPullback_spec hp)

include hq in
/-- A base change of a closed immersion is a closed immersion. -/
lemma isClosedImmersion_of_isPullback [IsClosedImmersion g] : IsClosedImmersion g' :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) hq inferInstance

include hp in
/-- Higher direct images of a pulled-back line bundle along a base change of `Spec.map φ`
vanish. -/
theorem isZero_higherDirectImage_pullback_lineBundle_of_isPullback (L : LineBundle X) (n : ℕ) :
    IsZero ((higherDirectImage p (n + 1)).obj ((Scheme.Modules.pullback p).obj L.obj)) :=
  have := isAffineHom_of_isPullback_spec hp
  isZero_higherDirectImage_pullback_of_isLocallyFreeRankOne p L.property n

include hp hq in
/-- Higher direct images of the pullback along `q` of the pullback along `g` of a line bundle
vanish, where `q` is the base change of a base change of `Spec.map φ`. -/
theorem isZero_higherDirectImage_pullback_pullback_lineBundle_of_isPullback (L : LineBundle X)
    (n : ℕ) :
    IsZero ((higherDirectImage q (n + 1)).obj
      ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj L.obj))) :=
  have := isAffineHom_of_isPullback_isPullback_spec hp hq
  isZero_higherDirectImage_pullback_of_isLocallyFreeRankOne q (L.property.pullback g) n

/-- The derived base change map of a line bundle `L` on `X` along the pullback square `hp`,
with its vanishing hypothesis discharged by
`isZero_higherDirectImage_pullback_lineBundle_of_isPullback`. -/
abbrev derivedBaseChangeMapLineBundle (L : LineBundle X) :
    (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).obj L.obj ⟶
      (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.obj
        ((DerivedPlus.derivedComplex (relativeGlobalSections f') ⋙ DerivedCategory.Plus.ι).obj
          ((Scheme.Modules.pullback p).obj L.obj)) :=
  derivedBaseChangeMap φ f f' p hp.w L.obj
    (isZero_higherDirectImage_pullback_lineBundle_of_isPullback hp L)

/-- For a line bundle `L` on `X`, a pullback square `p ≫ f = f' ≫ Spec.map φ`, a closed
immersion `g` and a pullback square `q ≫ g = g' ≫ p`, derived restriction along `g` and `g'`
commutes with derived base change along `p` and `q`. -/
theorem derivedRestrictionMap_comp_derivedBaseChangeMap_lineBundle_of_isPullback
    [IsClosedImmersion g] (L : LineBundle X) :
    haveI := isClosedImmersion_of_isPullback hq
    derivedRestrictionMap g f L.obj ≫
        derivedBaseChangeMap φ (g ≫ f) (g' ≫ f') q
          (square_restrict_comm φ f f' p hp.w g g' q hq.w) ((Scheme.Modules.pullback g).obj L.obj)
          (isZero_higherDirectImage_pullback_pullback_lineBundle_of_isPullback hp hq L) ≫
        (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
          ((DerivedPlus.derivedComplex (relativeGlobalSections (g' ≫ f')) ⋙
            DerivedCategory.Plus.ι).map ((pullbackSquareIso p g g' q hq.w).hom.app L.obj)) =
      derivedBaseChangeMapLineBundle hp L ≫
        (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
          (derivedRestrictionMap g' f' ((Scheme.Modules.pullback p).obj L.obj)) :=
  have := isClosedImmersion_of_isPullback hq
  have := isAffineHom_of_isPullback_spec hp
  have := isAffineHom_of_isPullback_isPullback_spec hp hq
  derivedRestrictionMap_comp_derivedBaseChangeMap_of_isLocallyFreeRankOne φ f f' p hp.w g g' q
    hq.w L.property

/-- Degreewise form of `derivedRestrictionMap_comp_derivedBaseChangeMap_lineBundle_of_isPullback`.
-/
theorem restrictionCohomologyMap_comp_baseChangeMap_lineBundle_of_isPullback
    [IsClosedImmersion g] (L : LineBundle X) (n : ℕ) :
    haveI := isClosedImmersion_of_isPullback hq
    restrictionCohomologyMap g f L.obj n ≫
        baseChangeMap φ (g ≫ f) (g' ≫ f') q (square_restrict_comm φ f f' p hp.w g g' q hq.w)
          ((Scheme.Modules.pullback g).obj L.obj)
          (isZero_higherDirectImage_pullback_pullback_lineBundle_of_isPullback hp hq L)
          (fun J hJ k => (pushforwardInjectiveAcyclic Y' Y q J hJ k).2 R (g ≫ f)) n ≫
        (ModuleCat.restrictScalars φ.hom).map ((relativeCohomology (g' ≫ f') n).map
          ((pullbackSquareIso p g g' q hq.w).hom.app L.obj)) =
      baseChangeMap φ f f' p hp.w L.obj
          (isZero_higherDirectImage_pullback_lineBundle_of_isPullback hp L)
          (fun J hJ k => (pushforwardInjectiveAcyclic X' X p J hJ k).2 R f) n ≫
        (ModuleCat.restrictScalars φ.hom).map
          (restrictionCohomologyMap g' f' ((Scheme.Modules.pullback p).obj L.obj) n) :=
  have := isClosedImmersion_of_isPullback hq
  have := isAffineHom_of_isPullback_spec hp
  have := isAffineHom_of_isPullback_isPullback_spec hp hq
  restrictionCohomologyMap_comp_baseChangeMap_of_isLocallyFreeRankOne φ f f' p hp.w g g' q
    hq.w L.property n

end IsPullback

end Langlands.AlgebraicGeometry.Modules.DerivedSections
