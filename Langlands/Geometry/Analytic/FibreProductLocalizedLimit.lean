import Langlands.Geometry.Analytic.FibreProductRefinedConeLift
import Langlands.Geometry.Analytic.LocalizedPullbackDescent

/-! # Same-universe localized limits of the actual small fibre-product cone -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Transport a full original cone identity through the actual saturation
isomorphisms, retaining equality of entire strong maps. -/
theorem saturationSourceLift_comp
    {R X : SaturatedAtlasPresentation.{u, v, v} K}
    {P : AffinoidAtlasPresentation.{u, v, v} K}
    (L : CompatibleStrongHom R.presentation P)
    (p : CompatibleStrongHom P X.presentation) (a : R ⟶ X)
    (h : L.comp p = geometricCompatibleMap a) :
    (R.saturationIso.inv ≫ (show ofSaturation R.presentation ⟶ ofSaturation P from L.saturationExtension)) ≫
      ((show ofSaturation P ⟶ ofSaturation X.presentation from p.saturationExtension) ≫
        X.saturationIso.hom) = a := by
  let L' : ofSaturation R.presentation ⟶ ofSaturation P := L.saturationExtension
  let p' : ofSaturation P ⟶ ofSaturation X.presentation := p.saturationExtension
  let a' : ofSaturation R.presentation ⟶ ofSaturation X.presentation :=
    (geometricCompatibleMap a).saturationExtension
  have he : L' ≫ p' = a' := by
    exact (CompatibleStrongHom.saturationExtension_comp L p).symm.trans
      (congrArg CompatibleStrongHom.saturationExtension h)
  have hn : a' ≫ X.saturationIso.hom =
      R.saturationIso.hom ≫ a := (saturationComparisonNatIso (K := K)).hom.naturality a
  change (R.saturationIso.inv ≫ L') ≫ (p' ≫ X.saturationIso.hom) = a
  calc
    (R.saturationIso.inv ≫ L') ≫
        (p' ≫ X.saturationIso.hom) =
      R.saturationIso.inv ≫
        ((L' ≫ p') ≫ X.saturationIso.hom) := by
          simp only [Category.assoc]
    _ = R.saturationIso.inv ≫ (R.saturationIso.hom ≫ a) := by rw [he, hn]
    _ = a := by rw [← Category.assoc, R.saturationIso.inv_hom_id, Category.id_comp]

variable {X Y S : SaturatedAtlasPresentation.{u, v, v} K}
  (f : X ⟶ S) (g : Y ⟶ S)
  [Small.{v} (FibreProduct.chartSystem (geometricCompatibleMap f) (geometricCompatibleMap g)).Space]

/-- Every full strong cone admits an actual same-universe strong lift after
the constructed full quasi-isomorphism original source refinement. -/
theorem smallFibreProduct_exists_refinedLift
    {T : SaturatedAtlasPresentation.{u, v, v} K}
    (a : T ⟶ X) (b : T ⟶ Y) (hab : a ≫ f = b ≫ g) :
    ∃ (R : SaturatedAtlasPresentation.{u, v, v} K) (s : R ⟶ T), s.IsQuasiIso ∧
      ∃ l : R ⟶ smallFibreProduct f g,
        l ≫ smallFibreProductFst f g = s ≫ a ∧
        l ≫ smallFibreProductSnd f g = s ≫ b := by
  let F := geometricCompatibleMap f
  let G := geometricCompatibleMap g
  let A := geometricCompatibleMap a
  let B := geometricCompatibleMap b
  have hAB : A.comp F = B.comp G := by
    exact (compatibleFunctor.map_comp a f).symm.trans
      ((congrArg compatibleFunctor.map hab).trans (compatibleFunctor.map_comp b g))
  let P := FibreProduct.coneSourceSelection F G A B
    X.hasAllLocalDomains Y.hasAllLocalDomains T.hasAllLocalDomains hAB
  let R := T.refiningSubpresentation P
  let s : R ⟶ T := T.refiningSubatlasInclusion P
  let L : CompatibleStrongHom R.presentation
      (FibreProduct.smallPresentation F G X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains) :=
    FibreProduct.refinedConeLift F G A B X.hasAllLocalDomains Y.hasAllLocalDomains
      S.hasAllLocalDomains T.hasAllLocalDomains hAB
  let l : R ⟶ smallFibreProduct f g := R.saturationIso.inv ≫ L.saturationExtension
  refine ⟨R, s, isQuasiIso_refiningSubatlasInclusion P, l, ?_, ?_⟩
  · apply saturationSourceLift_comp L
      (FibreProduct.smallFstHom F G X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains)
      (s ≫ a)
    exact (FibreProduct.refinedConeLift_comp_fst F G A B X.hasAllLocalDomains Y.hasAllLocalDomains
      S.hasAllLocalDomains T.hasAllLocalDomains hAB).trans
        ((CompatibleStrongHom.subatlasInclusion_comp A P.carrier P.locally_refining).symm.trans
          (compatibleFunctor.map_comp s a).symm)
  · apply saturationSourceLift_comp L
      (FibreProduct.smallSndHom F G X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains)
      (s ≫ b)
    exact (FibreProduct.refinedConeLift_comp_snd F G A B X.hasAllLocalDomains Y.hasAllLocalDomains
      S.hasAllLocalDomains T.hasAllLocalDomains hAB).trans
        ((CompatibleStrongHom.subatlasInclusion_comp B P.carrier P.locally_refining).symm.trans
          (compatibleFunctor.map_comp s b).symm)

/-- The actual small fibre-product cone has all full refined strong
universal-property data; no such data is assumed. -/
theorem smallFibreProduct_isRefinedStrongPullback :
    IsRefinedStrongPullback (smallFibreProductFst f g) (smallFibreProductSnd f g) f g :=
  ⟨smallFibreProduct_condition f g,
    fun _ a b hab => smallFibreProduct_exists_refinedLift f g a b hab,
    fun _ a b hp hq => smallFibreProduct_hom_ext f g a b hp hq⟩

/-- The entire same-universe square is a pullback among all objects and
arrows of the actual localized analytic category. -/
theorem smallFibreProduct_isPullback :
    IsPullback (localizationFunctor.map (smallFibreProductFst f g))
      (localizationFunctor.map (smallFibreProductSnd f g))
      (localizationFunctor.map f) (localizationFunctor.map g) :=
  (smallFibreProduct_isRefinedStrongPullback f g).isPullback

/-- The actual localized pullback cone carries its constructed limit. -/
def smallFibreProductLocalizedLimit :
    IsLimit (PullbackCone.mk (localizationFunctor.map (smallFibreProductFst f g))
      (localizationFunctor.map (smallFibreProductSnd f g))
      (by rw [← Functor.map_comp, ← Functor.map_comp, smallFibreProduct_condition])) :=
  (smallFibreProduct_isRefinedStrongPullback f g).isLimit

end Langlands.Analytic.SaturatedAtlasPresentation
