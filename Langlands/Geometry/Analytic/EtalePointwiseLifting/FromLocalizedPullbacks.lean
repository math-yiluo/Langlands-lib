import Langlands.Geometry.Analytic.FibreProductPoints
import Langlands.Geometry.Analytic.LocalizedEtalePullbackReduction
import Langlands.Geometry.Analytic.RecognizedLocalizedPullbacks
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteBanachPushout.Proof

/-! # Ordinary point lifting from localized étale pullbacks -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : SaturatedAtlasPresentation.{u, v, v} K}

private theorem recognitionSourceIso_inv_apply (f : A ⟶ C) (x : A.presentation.space) :
    localizedSpaceFunctor.map (recognitionSourceIso f).inv
      (x : (recognitionSource f).presentation.space) = x := by
  rw [recognitionSourceIso, localizedSpaceFunctor_map_quasiIso_inv]
  change (recognitionSourceComparison_isQuasiIso f).inverseBaseMap x = x
  have h := (recognitionSourceComparison_isQuasiIso f).baseMap_inverseBaseMap x
  rw [recognitionSourceComparison_baseMap] at h
  exact h

/-- The recognized pullback cone lifts all compatible ordinary point pairs
in the original independent field and space universes. -/
theorem exists_recognizedLocalizedPullback_point
    (f : A ⟶ C) (g : B ⟶ C) (hf : strongEtale f)
    (x : A.presentation.space) (y : B.presentation.space)
    (hxy : f.baseMap x = g.baseMap y) :
    let c := recognizedLocalizedPullback f g AffinoidPushout.finiteBanachPushout hf
    ∃ t : localizedSpaceFunctor.obj c.1.pt,
      localizedSpaceFunctor.map c.1.fst t = x ∧ localizedSpaceFunctor.map c.1.snd t = y := by
  let _ := recognition_fibreProductSpace_small f g AffinoidPushout.finiteBanachPushout hf
  let F := recognitionMap f
  let G := recognitionMap g
  let F' := geometricCompatibleMap F
  let G' := geometricCompatibleMap G
  obtain ⟨z, hz₁, hz₂⟩ := FibreProduct.exists_point F' G'
    (recognitionSource f).hasAllLocalDomains (recognitionSource g).hasAllLocalDomains x y hxy
  let e := FibreProduct.smallSpaceHomeomorph F' G'
    (recognitionSource f).hasAllLocalDomains (recognitionSource g).hasAllLocalDomains
    (recognitionBase C).hasAllLocalDomains
  let t : localizedSpaceFunctor.obj (localizationFunctor.obj (smallFibreProduct F G)) := e z
  refine ⟨t, ?_, ?_⟩
  · change localizedSpaceFunctor.map
      (localizationFunctor.map (smallFibreProductFst F G) ≫ (recognitionSourceIso f).inv)
      t = x
    rw [Functor.map_comp, TopCat.comp_app, localizedSpaceFunctor_map]
    change localizedSpaceFunctor.map (recognitionSourceIso f).inv
      (FibreProduct.fst F' G' (e.symm (e z))) = x
    rw [e.symm_apply_apply]
    exact (congrArg (fun s : (recognitionSource f).presentation.space =>
      localizedSpaceFunctor.map (recognitionSourceIso f).inv s) hz₁).trans
      (recognitionSourceIso_inv_apply f x)
  · change localizedSpaceFunctor.map
      (localizationFunctor.map (smallFibreProductSnd F G) ≫ (recognitionSourceIso g).inv)
      t = y
    rw [Functor.map_comp, TopCat.comp_app, localizedSpaceFunctor_map]
    change localizedSpaceFunctor.map (recognitionSourceIso g).inv
      (FibreProduct.snd F' G' (e.symm (e z))) = y
    rw [e.symm_apply_apply]
    exact (congrArg (fun s : (recognitionSource g).presentation.space =>
      localizedSpaceFunctor.map (recognitionSourceIso g).inv s) hz₂).trans
      (recognitionSourceIso_inv_apply g y)

set_option linter.defProp false in
/-- An étale localized pullback supplies the point-dependent strong square
required by the site assembly. -/
def strongEtalePointwiseBaseChange_of_localizedEtalePullback
    (hpullback : LocalizedEtalePullbackStatement.{u, v} K) :
    StrongEtalePointwiseBaseChangeStatement.{u, v} K := by
  intro A B C f g hf x y hxy
  obtain ⟨P, p, q, hP, hq⟩ := hpullback (localizationFunctor.map f) (localizationFunctor.map g) hf
  obtain ⟨T, a, b, hT, hb⟩ := exists_refinedStrongPullback_of_localized p q hP hq
  have hf' := (etale_localizationFunctor_map_iff_strongEtale f).mp hf
  let c := recognizedLocalizedPullback f g AffinoidPushout.finiteBanachPushout hf'
  obtain ⟨t, ht₁, ht₂⟩ := exists_recognizedLocalizedPullback_point f g hf' x y hxy
  obtain ⟨l, hl₁, hl₂⟩ := hT.exists_lift c.1.fst c.1.snd c.1.condition
  refine ⟨T, a, b, hT.1, etale_map_of_strongEtale b hb, localizedSpaceFunctor.map l t, ?_, ?_⟩
  · have hl := congrArg (fun k : c.1.pt ⟶ localizationFunctor.obj A =>
      localizedSpaceFunctor.map k t) hl₁
    rw [Functor.map_comp, TopCat.comp_app, localizedSpaceFunctor_map] at hl
    exact hl.trans ht₁
  · have hl := congrArg (fun k : c.1.pt ⟶ localizationFunctor.obj B =>
      localizedSpaceFunctor.map k t) hl₂
    rw [Functor.map_comp, TopCat.comp_app, localizedSpaceFunctor_map] at hl
    exact hl.trans ht₂

end Langlands.Analytic.SaturatedAtlasPresentation
