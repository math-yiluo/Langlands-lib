import Langlands.Geometry.Analytic.SaturatedEtaleProperty
import Langlands.Geometry.Analytic.SaturatedRightFractionComposition

/-! # Étale numerator conditions on actual localized right fractions -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : SaturatedAtlasPresentation.{u, v, w} K}

/-- Full quasi-isomorphisms cancel from actual category compositions on the right. -/
theorem isQuasiIso_of_comp_right {S T U : SaturatedAtlasPresentation.{u, v, w} K}
    {a : S ⟶ T} {s : T ⟶ U} (hs : s.IsQuasiIso)
    (has : (a ≫ s).IsQuasiIso) : a.IsQuasiIso :=
  hs.of_saturatedComp_right S.hasAllLocalDomains T.hasAllLocalDomains has

/-- Common refinement preserves the complete strong étale numerator condition. -/
theorem strongEtale_numerator_iff_of_commonRefinement
    {φ ψ : (quasiIsomorphisms (K := K)).RightFraction A B}
    (h : FractionCommonRefinement φ ψ) : strongEtale φ.f ↔ strongEtale ψ.f := by
  obtain ⟨S, a, b, hab, hnum, hden⟩ := h
  have ha : a.IsQuasiIso := isQuasiIso_of_comp_right φ.hs hden
  have hb : b.IsQuasiIso := isQuasiIso_of_comp_right ψ.hs (hab ▸ hden)
  rw [← strongEtale_precomp_quasiIso_iff (f := a) (g := φ.f) ha,
    ← strongEtale_precomp_quasiIso_iff (f := b) (g := ψ.f) hb, hnum]

/-- A localized arrow between presented objects has an étale numerator if
one of its actual right fractions has the canonical strong étale property. -/
def fractionEtale (h : localizationFunctor.obj A ⟶ localizationFunctor.obj B) : Prop :=
  ∃ φ : (quasiIsomorphisms (K := K)).RightFraction A B,
    h = localizedRightFraction φ ∧ strongEtale φ.f

/-- Any actual representative tests the same numerator condition. -/
theorem fractionEtale_localizedRightFraction_iff
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B) :
    fractionEtale (localizedRightFraction φ) ↔ strongEtale φ.f := by
  constructor
  · rintro ⟨ψ, hψ, hQψ⟩
    exact (strongEtale_numerator_iff_of_commonRefinement
      ((localizedRightFraction_eq_iff φ ψ).mp hψ)).mpr hQψ
  · intro hφ
    exact ⟨φ, rfl, hφ⟩

/-- For actual strong maps the right-fraction condition is exactly strong étaleness. -/
theorem fractionEtale_localizationFunctor_map_iff (f : A ⟶ B) :
    fractionEtale (localizationFunctor.map f) ↔ strongEtale f := by
  rw [← localizedRightFraction_ofHom f]
  exact fractionEtale_localizedRightFraction_iff _

/-- Ore composition carries strong étale numerators to strong étale numerators. -/
theorem strongEtale_rightFractionComp
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B)
    (ψ : (quasiIsomorphisms (K := K)).RightFraction B C)
    (hφ : strongEtale φ.f) (hψ : strongEtale ψ.f) :
    strongEtale (rightFractionComp φ ψ).f := by
  have hlift : strongEtale (quasiIsoOreLift φ.f ψ.s ψ.hs) := by
    apply (strongEtale_postcomp_quasiIso_iff ψ.hs).mp
    exact (congrArg (fun m => strongEtale m)
      (quasiIsoOre_square φ.f ψ.s ψ.hs)).mpr
        (strongEtale_comp
          (strongEtale_of_isQuasiIso _
            (isQuasiIso_quasiIsoOreInclusion φ.f ψ.s ψ.hs)) hφ)
  exact strongEtale_comp hlift hψ

/-- The intrinsic right-fraction condition composes on localized arrows. -/
theorem fractionEtale_comp
    {f : localizationFunctor.obj A ⟶ localizationFunctor.obj B}
    {g : localizationFunctor.obj B ⟶ localizationFunctor.obj C}
    (hf : fractionEtale f) (hg : fractionEtale g) : fractionEtale (f ≫ g) := by
  obtain ⟨φ, rfl, hφ⟩ := hf
  obtain ⟨ψ, rfl, hψ⟩ := hg
  exact ⟨rightFractionComp φ ψ, (localizedRightFraction_comp φ ψ).symm,
    strongEtale_rightFractionComp φ ψ hφ hψ⟩

/-- Identity localized arrows have the right-fraction étale condition. -/
theorem fractionEtale_id (A : SaturatedAtlasPresentation.{u, v, w} K) :
    fractionEtale (𝟙 (localizationFunctor.obj A)) := by
  rw [← localizationFunctor.map_id A, fractionEtale_localizationFunctor_map_iff]
  exact (strongEtale (K := K)).id_mem A

/-- Both maps of a localized denominator isomorphism have the numerator condition. -/
theorem fractionEtale_localizedQuasiIso_inv (s : A ⟶ B) (hs : s.IsQuasiIso) :
    fractionEtale (localizedQuasiIso s hs).inv := by
  let φ : (quasiIsomorphisms (K := K)).RightFraction B A := ⟨s, hs, 𝟙 A⟩
  refine ⟨φ, ?_, ?_⟩
  · change (localizedQuasiIso s hs).inv =
      (localizedQuasiIso s hs).inv ≫ localizationFunctor.map (𝟙 A)
    rw [localizationFunctor.map_id, Category.comp_id]
  · exact (strongEtale (K := K)).id_mem A

/-- The intrinsic right-fraction numerator condition on every object of the
actual localization, using its fixed object bijection. -/
def localizedFractionEtale : MorphismProperty (LocalizedCategory.{u, v, w} (K := K)) :=
  fun X Y h => fractionEtale
    (A := localizedObjectEquiv.symm X) (B := localizedObjectEquiv.symm Y)
    (eqToHom (localizedObjectEquiv.apply_symm_apply X) ≫ h ≫
      eqToHom (localizedObjectEquiv.apply_symm_apply Y).symm)

/-- On presented objects the global property is precisely the fraction test. -/
@[simp]
theorem localizedFractionEtale_iff
    (f : localizationFunctor.obj A ⟶ localizationFunctor.obj B) :
    localizedFractionEtale f ↔ fractionEtale f := by
  change fractionEtale (𝟙 _ ≫ f ≫ 𝟙 _) ↔ fractionEtale f
  rw [Category.id_comp, Category.comp_id]

instance : (localizedFractionEtale (K := K) :
    MorphismProperty (LocalizedCategory.{u, v, w} (K := K))).IsMultiplicative where
  id_mem X := by
    obtain ⟨A, rfl⟩ := localizedObjectEquiv.surjective X
    exact (localizedFractionEtale_iff _).mpr (fractionEtale_id A)
  comp_mem {X Y Z} f g hf hg := by
    obtain ⟨A, rfl⟩ := localizedObjectEquiv.surjective X
    obtain ⟨B, rfl⟩ := localizedObjectEquiv.surjective Y
    obtain ⟨C, rfl⟩ := localizedObjectEquiv.surjective Z
    exact (localizedFractionEtale_iff _).mpr (fractionEtale_comp
      ((localizedFractionEtale_iff _).mp hf) ((localizedFractionEtale_iff _).mp hg))

/-- The localized condition agrees exactly with the canonical strong property
on images of actual strong morphisms. -/
@[simp]
theorem localizedFractionEtale_map_iff (f : A ⟶ B) :
    localizedFractionEtale (localizationFunctor.map f) ↔ strongEtale f :=
  (localizedFractionEtale_iff _).trans (fractionEtale_localizationFunctor_map_iff f)

/-- The inverse of every actual denominator is in the global fraction property. -/
theorem localizedFractionEtale_quasiIso_inv (s : A ⟶ B) (hs : s.IsQuasiIso) :
    localizedFractionEtale (localizedQuasiIso s hs).inv :=
  (localizedFractionEtale_iff _).mpr (fractionEtale_localizedQuasiIso_inv s hs)

/-- Quasi-isomorphism images preserve and reflect the global fraction property
under source composition, for arbitrary localized targets. -/
theorem localizedFractionEtale_precomp_quasiIso_iff
    (s : A ⟶ B) (hs : s.IsQuasiIso)
    {X : LocalizedCategory.{u, v, w} (K := K)}
    (f : localizationFunctor.obj B ⟶ X) :
    localizedFractionEtale (localizationFunctor.map s ≫ f) ↔ localizedFractionEtale f := by
  constructor
  · intro h
    have hh := (localizedFractionEtale (K := K)).comp_mem
      (localizedQuasiIso s hs).inv _ (localizedFractionEtale_quasiIso_inv s hs) h
    simpa only [← Category.assoc, localizedQuasiIso_inv_hom_id, Category.id_comp] using hh
  · intro h
    exact (localizedFractionEtale (K := K)).comp_mem _ _
      ((localizedFractionEtale_map_iff s).mpr (strongEtale_of_isQuasiIso s hs)) h

/-- Quasi-isomorphism images preserve and reflect the global fraction property
under target composition, for arbitrary localized sources. -/
theorem localizedFractionEtale_postcomp_quasiIso_iff
    (s : A ⟶ B) (hs : s.IsQuasiIso)
    {X : LocalizedCategory.{u, v, w} (K := K)}
    (f : X ⟶ localizationFunctor.obj A) :
    localizedFractionEtale (f ≫ localizationFunctor.map s) ↔ localizedFractionEtale f := by
  constructor
  · intro h
    have hh := (localizedFractionEtale (K := K)).comp_mem _
      (localizedQuasiIso s hs).inv h (localizedFractionEtale_quasiIso_inv s hs)
    simpa only [Category.assoc, localizedQuasiIso_hom_inv_id, Category.comp_id] using hh
  · intro h
    exact (localizedFractionEtale (K := K)).comp_mem _ _ h
      ((localizedFractionEtale_map_iff s).mpr (strongEtale_of_isQuasiIso s hs))

end Langlands.Analytic.SaturatedAtlasPresentation
