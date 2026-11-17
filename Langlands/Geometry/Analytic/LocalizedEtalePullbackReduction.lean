import Langlands.Geometry.Analytic.LocalizedPullbackDescent
import Langlands.Geometry.Analytic.LocalizedEtaleComposition
import Langlands.Geometry.Analytic.EtaleGeometricPointPullbacks

/-! # Exact strong-map reduction for localized étale pullbacks -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A mapped strong square is a localized pullback only if it has refined
strong existence and complete strong joint uniqueness. -/
theorem isRefinedStrongPullback_of_isPullback
    {A B C P : SaturatedAtlasPresentation.{u, v, w} K}
    {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (h : IsPullback (localizationFunctor.map p) (localizationFunctor.map q)
      (localizationFunctor.map f) (localizationFunctor.map g)) :
    IsRefinedStrongPullback p q f g := by
  refine ⟨?_, ?_, ?_⟩
  · apply localizationFunctor_map_injective
    change localizationFunctor.map (p ≫ f) = localizationFunctor.map (q ≫ g)
    simpa only [Functor.map_comp] using h.w
  · intro T a b hab
    have hab' : localizationFunctor.map a ≫ localizationFunctor.map f =
        localizationFunctor.map b ≫ localizationFunctor.map g := by
      rw [← Functor.map_comp, ← Functor.map_comp, hab]
    obtain ⟨l, hlp, hlq⟩ := h.exists_lift _ _ hab'
    obtain ⟨φ, rfl⟩ := exists_localizedRightFraction l
    refine ⟨φ.X', φ.s, φ.hs, φ.f, ?_, ?_⟩
    · apply localizationFunctor_map_injective
      change localizationFunctor.map (φ.f ≫ p) = localizationFunctor.map (φ.s ≫ a)
      rw [Functor.map_comp, Functor.map_comp,
        ← localizationFunctor_map_s_comp_localizedRightFraction φ,
        Category.assoc, hlp]
    · apply localizationFunctor_map_injective
      change localizationFunctor.map (φ.f ≫ q) = localizationFunctor.map (φ.s ≫ b)
      rw [Functor.map_comp, Functor.map_comp,
        ← localizationFunctor_map_s_comp_localizedRightFraction φ,
        Category.assoc, hlq]
  · intro T a b hp hq
    apply localizationFunctor_map_injective
    apply h.hom_ext
    · rw [← Functor.map_comp, ← Functor.map_comp, hp]
    · rw [← Functor.map_comp, ← Functor.map_comp, hq]

/-- Refined strong pullback data are exactly the actual localized universal
property of a mapped strong square. -/
theorem isRefinedStrongPullback_iff_isPullback
    {A B C P : SaturatedAtlasPresentation.{u, v, w} K}
    (p : P ⟶ A) (q : P ⟶ B) (f : A ⟶ C) (g : B ⟶ C) :
    IsRefinedStrongPullback p q f g ↔
      IsPullback (localizationFunctor.map p) (localizationFunctor.map q)
        (localizationFunctor.map f) (localizationFunctor.map g) :=
  ⟨fun h => h.isPullback, isRefinedStrongPullback_of_isPullback⟩

/-- Strong-map form of the same-universe étale pullback existence problem. -/
def RefinedStrongEtalePullbackStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ {A B X : SaturatedAtlasPresentation.{u, v, v} K} (f : A ⟶ X) (g : B ⟶ X),
    strongEtale f →
    ∃ (P : SaturatedAtlasPresentation.{u, v, v} K) (p : P ⟶ A) (q : P ⟶ B),
      IsRefinedStrongPullback p q f g ∧ strongEtale q

/-- An actual étale localized pullback of strong arrows can be represented
by a refined strong square without changing any universe. -/
theorem exists_refinedStrongPullback_of_localized
    {A B C : SaturatedAtlasPresentation.{u, v, v} K}
    {f : A ⟶ C} {g : B ⟶ C}
    {Z : LocalizedCategory.{u, v, v} (K := K)}
    (p : Z ⟶ localizationFunctor.obj A) (q : Z ⟶ localizationFunctor.obj B)
    (h : IsPullback p q (localizationFunctor.map f) (localizationFunctor.map g))
    (hq : etale q) :
    ∃ (P : SaturatedAtlasPresentation.{u, v, v} K) (p' : P ⟶ A) (q' : P ⟶ B),
      IsRefinedStrongPullback p' q' f g ∧ strongEtale q' := by
  obtain ⟨T, hT⟩ := localizedObjectEquiv.surjective Z
  change localizationFunctor.obj T = Z at hT
  subst Z
  obtain ⟨S, s, hs, a, b, ha, hb⟩ := exists_commonStrongNumerators p q
  have h' : IsPullback (localizationFunctor.map a) (localizationFunctor.map b)
      (localizationFunctor.map f) (localizationFunctor.map g) := by
    apply h.of_iso' (localizedQuasiIso s hs) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simpa only [Iso.refl_hom, localizedQuasiIso_hom, Category.comp_id] using ha
    · simpa only [Iso.refl_hom, localizedQuasiIso_hom, Category.comp_id] using hb
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  refine ⟨S, a, b, isRefinedStrongPullback_of_isPullback h', ?_⟩
  apply (etale_localizationFunctor_map_iff_strongEtale b).mp
  rw [← hb]
  have : IsIso (localizationFunctor.map s) := (localizedQuasiIso s hs).isIso_hom
  exact etale_comp (etale_of_isIso _) hq

/-- The strong-map existence problem implies the original actual localized
étale pullback target, including arbitrary fraction cospans. -/
theorem localizedEtalePullbackStatement_of_refinedStrong
    (h : RefinedStrongEtalePullbackStatement.{u, v} K) :
    LocalizedEtalePullbackStatement.{u, v} K := by
  intro A B X f g hf
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
  obtain ⟨P, p, q, hP, hq⟩ := h φ.f ψ.f hφ
  refine ⟨localizationFunctor.obj P, localizationFunctor.map p ≫ localizationFunctor.map φ.s,
    localizationFunctor.map q ≫ localizationFunctor.map ψ.s, ?_, ?_⟩
  · apply hP.isPullback.of_iso (Iso.refl _) (localizedQuasiIso φ.s φ.hs)
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
  · exact etale_comp ((etale_localizationFunctor_map_iff_strongEtale q).mpr hq)
      (etale_of_isIso _)

/-- The remaining strong geometric construction is equivalent to the exact
original localized theorem. -/
theorem refinedStrongEtalePullbackStatement_iff :
    RefinedStrongEtalePullbackStatement.{u, v} K ↔
      LocalizedEtalePullbackStatement.{u, v} K := by
  refine ⟨localizedEtalePullbackStatement_of_refinedStrong, ?_⟩
  intro h A B X f g hf
  obtain ⟨Z, p, q, hP, hq⟩ := h (localizationFunctor.map f)
    (localizationFunctor.map g) ((etale_localizationFunctor_map_iff_strongEtale f).mpr hf)
  exact exists_refinedStrongPullback_of_localized p q hP hq

end Langlands.Analytic.SaturatedAtlasPresentation
