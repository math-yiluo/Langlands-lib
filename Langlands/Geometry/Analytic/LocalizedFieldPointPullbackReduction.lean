import Langlands.Geometry.Analytic.LocalizedPullbackDescent
import Langlands.Geometry.Analytic.LocalizedEtaleComposition
import Langlands.Geometry.Analytic.EtaleGeometricPointPullbacks

/-! # Strong-map reduction for full field-point pullback preservation -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type uL) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]
  [NormedAlgebra K L]

/-- The full localized field-point functor preserves every pullback square
of mapped strong morphisms whose strong left leg is étale. -/
def StrongEtaleFieldPointPullbackStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type uL) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]
    [NormedAlgebra K L] : Prop :=
  ∀ {P A B X : SaturatedAtlasPresentation.{u, v, v} K}
    (p : P ⟶ A) (q : P ⟶ B) (f : A ⟶ X) (g : B ⟶ X),
    strongEtale f →
    IsPullback (localizationFunctor.map p) (localizationFunctor.map q)
      (localizationFunctor.map f) (localizationFunctor.map g) →
    IsPullback ((localizedFieldPointFunctor L).map (localizationFunctor.map p))
      ((localizedFieldPointFunctor L).map (localizationFunctor.map q))
      ((localizedFieldPointFunctor L).map (localizationFunctor.map f))
      ((localizedFieldPointFunctor L).map (localizationFunctor.map g))

/-- Full field-point preservation for mapped strong squares suffices for
arbitrary pullbacks in the actual localization, including fraction cospans. -/
theorem localizedEtaleFieldPointPullbackStatement_of_strong
    (h : StrongEtaleFieldPointPullbackStatement.{u, v, uL} K L) :
    LocalizedEtaleFieldPointPullbackStatement.{u, v, uL} K L := by
  intro P A B X p q f g hf hP
  obtain ⟨P', hP'⟩ := localizedObjectEquiv.surjective P
  change localizationFunctor.obj P' = P at hP'
  subst P
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
  obtain ⟨S, s, hs, a, b, ha, hb⟩ := exists_commonStrongNumerators
    (p ≫ (localizedQuasiIso φ.s φ.hs).inv)
    (q ≫ (localizedQuasiIso ψ.s ψ.hs).inv)
  have hpa : localizationFunctor.map s ≫ p =
      localizationFunctor.map a ≫ localizationFunctor.map φ.s := by
    have he := congrArg (fun k => k ≫ (localizedQuasiIso φ.s φ.hs).hom) ha
    have he' : localizationFunctor.map s ≫ p =
        localizationFunctor.map a ≫ (localizedQuasiIso φ.s φ.hs).hom := by
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using he
    exact he'.trans (congrArg (fun k => localizationFunctor.map a ≫ k)
      (localizedQuasiIso_hom φ.s φ.hs))
  have hqb : localizationFunctor.map s ≫ q =
      localizationFunctor.map b ≫ localizationFunctor.map ψ.s := by
    have he := congrArg (fun k => k ≫ (localizedQuasiIso ψ.s ψ.hs).hom) hb
    have he' : localizationFunctor.map s ≫ q =
        localizationFunctor.map b ≫ (localizedQuasiIso ψ.s ψ.hs).hom := by
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using he
    exact he'.trans (congrArg (fun k => localizationFunctor.map b ≫ k)
      (localizedQuasiIso_hom ψ.s ψ.hs))
  have hφ : strongEtale φ.f := by
    apply (etale_localizationFunctor_map_iff_strongEtale φ.f).mp
    rw [← localizationFunctor_map_s_comp_localizedRightFraction φ]
    exact etale_comp (etale_of_isIso _) hf
  have hS : IsPullback (localizationFunctor.map a) (localizationFunctor.map b)
      (localizationFunctor.map φ.f) (localizationFunctor.map ψ.f) := by
    apply hP.of_iso' (localizedQuasiIso s hs) (localizedQuasiIso φ.s φ.hs)
      (localizedQuasiIso ψ.s ψ.hs) (Iso.refl _)
    · exact hpa
    · exact hqb
    · change localizationFunctor.map φ.s ≫ localizedRightFraction φ =
        localizationFunctor.map φ.f ≫ 𝟙 _
      rw [Category.comp_id]
      exact localizationFunctor_map_s_comp_localizedRightFraction φ
    · change localizationFunctor.map ψ.s ≫ localizedRightFraction ψ =
        localizationFunctor.map ψ.f ≫ 𝟙 _
      rw [Category.comp_id]
      exact localizationFunctor_map_s_comp_localizedRightFraction ψ
  let F := localizedFieldPointFunctor (K := K) L
  apply (h a b φ.f ψ.f hφ hS).of_iso (F.mapIso (localizedQuasiIso s hs))
    (F.mapIso (localizedQuasiIso φ.s φ.hs))
    (F.mapIso (localizedQuasiIso ψ.s ψ.hs)) (F.mapIso (Iso.refl _))
  · change F.map (localizationFunctor.map a) ≫ F.map (localizationFunctor.map φ.s) =
      F.map (localizationFunctor.map s) ≫ F.map p
    rw [← F.map_comp, ← F.map_comp, hpa]
  · change F.map (localizationFunctor.map b) ≫ F.map (localizationFunctor.map ψ.s) =
      F.map (localizationFunctor.map s) ≫ F.map q
    rw [← F.map_comp, ← F.map_comp, hqb]
  · change F.map (localizationFunctor.map φ.f) ≫ F.map (𝟙 _) =
      F.map (localizationFunctor.map φ.s) ≫ F.map (localizedRightFraction φ)
    rw [← F.map_comp, ← F.map_comp, Category.comp_id,
      localizationFunctor_map_s_comp_localizedRightFraction]
  · change F.map (localizationFunctor.map ψ.f) ≫ F.map (𝟙 _) =
      F.map (localizationFunctor.map ψ.s) ≫ F.map (localizedRightFraction ψ)
    rw [← F.map_comp, ← F.map_comp, Category.comp_id,
      localizationFunctor_map_s_comp_localizedRightFraction]

/-- The strong-square preservation problem is exactly the original full
field-point pullback-preservation target, with all universes unchanged. -/
theorem strongEtaleFieldPointPullbackStatement_iff :
    StrongEtaleFieldPointPullbackStatement.{u, v, uL} K L ↔
      LocalizedEtaleFieldPointPullbackStatement.{u, v, uL} K L := by
  refine ⟨localizedEtaleFieldPointPullbackStatement_of_strong L, ?_⟩
  intro h P A B X p q f g hf hP
  exact h _ _ _ _ ((etale_localizationFunctor_map_iff_strongEtale f).mpr hf) hP

end Langlands.Analytic.SaturatedAtlasPresentation
