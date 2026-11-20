import Langlands.Geometry.Analytic.EtalePointwiseLifting.FromLocalizedPullbacks

/-! # Underlying points in pullbacks along étale analytic maps -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Compatible ordinary points lift to any analytic pullback with an étale first leg. -/
theorem exists_point_of_isPullback_of_etale
    {P A B X : LocalizedCategory.{u, v, v} (K := K)}
    {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ X} {g : B ⟶ X}
    (h : IsPullback p q f g) (hf : etale f)
    (x : localizedSpaceFunctor.obj A) (y : localizedSpaceFunctor.obj B)
    (hxy : localizedSpaceFunctor.map f x = localizedSpaceFunctor.map g y) :
    ∃ z : localizedSpaceFunctor.obj P,
      localizedSpaceFunctor.map p z = x ∧ localizedSpaceFunctor.map q z = y := by
  obtain ⟨A₀, hA⟩ := localizedObjectEquiv.surjective A
  change localizationFunctor.obj A₀ = A at hA
  subst A
  obtain ⟨B₀, hB⟩ := localizedObjectEquiv.surjective B
  change localizationFunctor.obj B₀ = B at hB
  subst B
  obtain ⟨X₀, hX⟩ := localizedObjectEquiv.surjective X
  change localizationFunctor.obj X₀ = X at hX
  subst X
  obtain ⟨φ, rfl⟩ := exists_localizedRightFraction f
  obtain ⟨ψ, rfl⟩ := exists_localizedRightFraction g
  have hφ : strongEtale φ.f := by
    have : IsIso (localizationFunctor.map φ.s) := (localizedQuasiIso φ.s φ.hs).isIso_hom
    apply (etale_localizationFunctor_map_iff_strongEtale φ.f).mp
    rw [← localizationFunctor_map_s_comp_localizedRightFraction φ]
    exact MorphismProperty.RespectsIso.precomp etale (localizationFunctor.map φ.s) _ hf
  have hxy' : φ.f.baseMap (φ.hs.inverseBaseMap x) = ψ.f.baseMap (ψ.hs.inverseBaseMap y) := by
    rw [localizedSpaceFunctor_map_rightFraction, localizedSpaceFunctor_map_rightFraction] at hxy
    exact hxy
  let c := recognizedLocalizedPullback φ.f ψ.f AffinoidPushout.finiteBanachPushout hφ
  obtain ⟨z, hz₁, hz₂⟩ := exists_recognizedLocalizedPullback_point φ.f ψ.f hφ
    (φ.hs.inverseBaseMap x) (ψ.hs.inverseBaseMap y) hxy'
  have hz₁' : localizedSpaceFunctor.map (c.1.fst ≫ localizationFunctor.map φ.s) z = x := by
    rw [Functor.map_comp, TopCat.comp_app, hz₁, localizedSpaceFunctor_map]
    exact φ.hs.baseMap_inverseBaseMap x
  have hz₂' : localizedSpaceFunctor.map (c.1.snd ≫ localizationFunctor.map ψ.s) z = y := by
    rw [Functor.map_comp, TopCat.comp_app, hz₂, localizedSpaceFunctor_map]
    exact ψ.hs.baseMap_inverseBaseMap y
  have hc : (c.1.fst ≫ localizationFunctor.map φ.s) ≫ localizedRightFraction φ =
      (c.1.snd ≫ localizationFunctor.map ψ.s) ≫ localizedRightFraction ψ := by
    simp only [Category.assoc, localizationFunctor_map_s_comp_localizedRightFraction]
    exact c.1.condition
  obtain ⟨l, h₁, h₂⟩ := h.exists_lift _ _ hc
  refine ⟨localizedSpaceFunctor.map l z, ?_, ?_⟩
  · rw [← TopCat.comp_app, ← Functor.map_comp, h₁]
    exact hz₁'
  · rw [← TopCat.comp_app, ← Functor.map_comp, h₂]
    exact hz₂'

/-- Point lifting in analytic pullbacks along étale morphisms with independent field and space universes. -/
def LocalizedEtalePullbackPointsStatement : Prop :=
  ∀ {P A B X : LocalizedCategory.{u, v, v} (K := K)}
    {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ X} {g : B ⟶ X},
    IsPullback p q f g → etale f →
    ∀ (x : localizedSpaceFunctor.obj A) (y : localizedSpaceFunctor.obj B),
      localizedSpaceFunctor.map f x = localizedSpaceFunctor.map g y →
        ∃ z : localizedSpaceFunctor.obj P,
          localizedSpaceFunctor.map p z = x ∧ localizedSpaceFunctor.map q z = y

theorem localizedEtalePullbackPoints : LocalizedEtalePullbackPointsStatement.{u, v} (K := K) :=
  fun h hf x y hxy => exists_point_of_isPullback_of_etale h hf x y hxy

end Langlands.Analytic.SaturatedAtlasPresentation
