import Langlands.Geometry.Analytic.RecognizedLocalizedPullbacks
import Langlands.Geometry.Analytic.LocalizedEtaleComposition
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteBanachPushout.Proof

/-! # Same-universe pullback existence along localized etale maps -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Pullbacks along any etale arrow exist among all objects and morphisms
of the actual localization, with the original common space/index universe. -/
theorem exists_localizedPullback_of_etale
    {A B X : LocalizedCategory.{u, v, v} (K := K)}
    (f : A ⟶ X) (g : B ⟶ X) (hf : etale f) :
    ∃ (P : LocalizedCategory.{u, v, v} (K := K)) (p : P ⟶ A) (q : P ⟶ B),
      IsPullback p q f g := by
  obtain ⟨A', hA⟩ := localizedObjectEquiv.surjective A
  change localizationFunctor.obj A' = A at hA
  subst A
  obtain ⟨B', hB⟩ := localizedObjectEquiv.surjective B
  change localizationFunctor.obj B' = B at hB
  subst B
  obtain ⟨X', hX⟩ := localizedObjectEquiv.surjective X
  change localizationFunctor.obj X' = X at hX
  subst X
  obtain ⟨φ, rfl⟩ := exists_localizedRightFraction f
  obtain ⟨ψ, rfl⟩ := exists_localizedRightFraction g
  have : IsIso (localizationFunctor.map φ.s) := (localizedQuasiIso φ.s φ.hs).isIso_hom
  have : IsIso (localizationFunctor.map ψ.s) := (localizedQuasiIso ψ.s ψ.hs).isIso_hom
  have hφ : strongEtale φ.f := by
    apply (etale_localizationFunctor_map_iff_strongEtale φ.f).mp
    rw [← localizationFunctor_map_s_comp_localizedRightFraction φ]
    exact etale_comp (etale_of_isIso _) hf
  obtain ⟨P, p, q, hP⟩ := exists_localizedPullback_of_strongEtale φ.f ψ.f
    AffinoidPushout.finiteBanachPushout hφ
  refine ⟨P, p ≫ localizationFunctor.map φ.s, q ≫ localizationFunctor.map ψ.s, ?_⟩
  apply hP.of_iso (Iso.refl _) (localizedQuasiIso φ.s φ.hs)
    (localizedQuasiIso ψ.s ψ.hs) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · change localizationFunctor.map φ.f ≫ 𝟙 _ =
      localizationFunctor.map φ.s ≫ localizedRightFraction φ
    simpa only [Category.comp_id] using
      (localizationFunctor_map_s_comp_localizedRightFraction φ).symm
  · change localizationFunctor.map ψ.f ≫ 𝟙 _ =
      localizationFunctor.map ψ.s ≫ localizedRightFraction ψ
    simpa only [Category.comp_id] using
      (localizationFunctor_map_s_comp_localizedRightFraction ψ).symm

/-- Choose an actual limiting cone over any cospan with an etale first leg.
All geometric size and full strong-map lifting obligations are proved. -/
def localizedEtalePullback
    {A B X : LocalizedCategory.{u, v, v} (K := K)}
    (f : A ⟶ X) (g : B ⟶ X) (hf : etale f) :
    Σ c : PullbackCone f g, IsLimit c :=
  Classical.choice (show Nonempty (Σ c : PullbackCone f g, IsLimit c) from by
    obtain ⟨P, p, q, hP⟩ := exists_localizedPullback_of_etale f g hf
    exact ⟨⟨PullbackCone.mk p q hP.w, hP.isLimit⟩⟩)

end Langlands.Analytic.SaturatedAtlasPresentation
