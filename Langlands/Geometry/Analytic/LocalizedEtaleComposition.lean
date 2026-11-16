import Langlands.Geometry.Analytic.SaturatedLocalizedIsomorphisms
import Langlands.Geometry.Analytic.SaturatedEtaleComparison

/-! # Composition for the actual localized étale predicate -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Every isomorphism in the actual localization has the intrinsic
étale numerator property. -/
theorem localizedFractionEtale_of_isIso
    {X Y : LocalizedCategory.{u, v, w} (K := K)} (f : X ⟶ Y) [IsIso f] :
    localizedFractionEtale f := by
  let e := asIso f
  obtain ⟨A, rfl⟩ := localizedObjectEquiv.surjective X
  obtain ⟨B, rfl⟩ := localizedObjectEquiv.surjective Y
  let φ := quasiIsoFractionOfIso e
  exact (localizedFractionEtale_iff f).mpr
    ⟨φ.val, (localizedRightFraction_quasiIsoFractionOfIso e).symm,
      strongEtale_of_isQuasiIso φ.val.f φ.property⟩

instance : (localizedFractionEtale (K := K) :
    MorphismProperty (LocalizedCategory.{u, v, w} (K := K))).RespectsIso where
  precomp e he f hf := by
    have : IsIso e := he
    exact (localizedFractionEtale (K := K)).comp_mem _ _
      (localizedFractionEtale_of_isIso e) hf
  postcomp e he f hf := by
    have : IsIso e := he
    exact (localizedFractionEtale (K := K)).comp_mem _ _ hf
      (localizedFractionEtale_of_isIso e)

/-- The intrinsic numerator condition is exactly the existing localized
étale predicate, with independent field and space universes. -/
theorem localizedFractionEtale_eq_etale :
    (localizedFractionEtale (K := K) :
      MorphismProperty (LocalizedCategory.{u, v, v} (K := K))) = etale := by
  rw [etale_eq_isoClosure_localizedFractionEtale, MorphismProperty.isoClosure_eq_self]

/-- Étale arrows in the actual analytic localization compose. -/
theorem etale_comp {X Y Z : LocalizedCategory.{u, v, v} (K := K)}
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : etale f) (hg : etale g) : etale (f ≫ g) := by
  rw [← localizedFractionEtale_eq_etale] at hf hg ⊢
  exact (localizedFractionEtale (K := K)).comp_mem f g hf hg

instance : (etale (K := K)).IsStableUnderComposition where
  comp_mem _ _ hf hg := etale_comp hf hg

/-- The existing étale property of an actual mapped arrow is precisely
its canonical strong étale condition. -/
theorem etale_localizationFunctor_map_iff_strongEtale
    {A B : SaturatedAtlasPresentation.{u, v, v} K} (f : A ⟶ B) :
    etale (localizationFunctor.map f) ↔ strongEtale f := by
  rw [← localizedFractionEtale_eq_etale]
  exact localizedFractionEtale_map_iff f

/-- For constructed saturations this is exactly the original geometric
all-pieces condition on the supplied strong morphism. -/
theorem etale_localizationFunctor_map_ofSaturation_iff
    {A B : AffinoidAtlasPresentation.{u, v, v} K}
    (f : ofSaturation A ⟶ ofSaturation B) :
    etale (localizationFunctor.map f) ↔
      StrongHom.IsEtaleAllPieces (A := A) (B := B) f :=
  (etale_localizationFunctor_map_iff_strongEtale f).trans (strongEtale_ofSaturation_iff f)

/-- Strong right cancellation transports through exact fractions to the
existing localized étale predicate. The strong geometric input is explicit. -/
theorem etale_hasOfPostcompProperty_of_strong
    (hStrong : (strongEtale (K := K) :
      MorphismProperty (SaturatedAtlasPresentation.{u, v, v} K)).HasOfPostcompProperty
        (strongEtale (K := K))) :
    (etale (K := K) : MorphismProperty
      (LocalizedCategory.{u, v, v} (K := K))).HasOfPostcompProperty (etale (K := K)) := by
  refine ⟨?_⟩
  intro X Y Z f g hg hfg
  obtain ⟨A, rfl⟩ := localizedObjectEquiv.surjective X
  obtain ⟨B, rfl⟩ := localizedObjectEquiv.surjective Y
  obtain ⟨C, rfl⟩ := localizedObjectEquiv.surjective Z
  rw [← localizedFractionEtale_eq_etale] at hg hfg ⊢
  obtain ⟨φ, rfl⟩ := exists_localizedRightFraction f
  obtain ⟨ψ, rfl⟩ := exists_localizedRightFraction g
  have hψ : strongEtale ψ.f := (fractionEtale_localizedRightFraction_iff ψ).mp
    ((localizedFractionEtale_iff _).mp hg)
  have hφψ : strongEtale (rightFractionComp φ ψ).f :=
    (fractionEtale_localizedRightFraction_iff _).mp
      ((localizedFractionEtale_iff _).mp
        ((congrArg (fun m => localizedFractionEtale m)
          (localizedRightFraction_comp φ ψ)).mpr hfg))
  have hlift : strongEtale (quasiIsoOreLift φ.f ψ.s ψ.hs) :=
    hStrong.of_postcomp _ ψ.f hψ hφψ
  have hcomp : strongEtale (quasiIsoOreInclusion φ.f ψ.s ψ.hs ≫ φ.f) :=
    (congrArg (fun m => strongEtale m) (quasiIsoOre_square φ.f ψ.s ψ.hs)).mp
      (strongEtale_comp hlift (strongEtale_of_isQuasiIso ψ.s ψ.hs))
  have hφ : strongEtale φ.f := (strongEtale_precomp_quasiIso_iff
    (isQuasiIso_quasiIsoOreInclusion φ.f ψ.s ψ.hs)).mp hcomp
  exact (localizedFractionEtale_iff _).mpr
    ((fractionEtale_localizedRightFraction_iff φ).mpr hφ)

end Langlands.Analytic.SaturatedAtlasPresentation
