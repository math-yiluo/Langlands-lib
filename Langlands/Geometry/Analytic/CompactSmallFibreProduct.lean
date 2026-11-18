import Langlands.Geometry.Analytic.CompactFibreProduct
import Langlands.Geometry.Analytic.LocalizedEtalePullbackExistence

/-! # Compact analytic pullbacks along étale morphisms -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Compact Hausdorffness is invariant under localized analytic isomorphisms. -/
theorem IsCompactSpace.of_iso {A B : LocalizedCategory.{u, v, v} (K := K)}
    (hA : IsCompactSpace A) (e : A ≅ B) : IsCompactSpace B := by
  let := hA.1
  let := hA.2
  let h := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso e)
  exact ⟨h.compactSpace, h.t2Space⟩

section Strong

variable {A B C : SaturatedAtlasPresentation.{u, v, v} K}
  (f : A ⟶ C) (g : B ⟶ C)

/-- The existing small saturated fibre product is compact Hausdorff when
the two factors are compact Hausdorff and the base is Hausdorff. -/
theorem isCompactSpace_localization_smallFibreProduct
    [Small.{v} (FibreProduct.chartSystem (geometricCompatibleMap f) (geometricCompatibleMap g)).Space]
    [CompactSpace A.presentation.space] [CompactSpace B.presentation.space]
    [T2Space A.presentation.space] [T2Space B.presentation.space]
    [T2Space C.presentation.space] :
    IsCompactSpace (localizationFunctor.obj (smallFibreProduct f g)) := by
  let F := geometricCompatibleMap f
  let G := geometricCompatibleMap g
  let := FibreProduct.compactSpace F G A.hasAllLocalDomains B.hasAllLocalDomains
  let := FibreProduct.t2Space F G A.hasAllLocalDomains B.hasAllLocalDomains
  let h := FibreProduct.smallSpaceHomeomorph F G
    A.hasAllLocalDomains B.hasAllLocalDomains C.hasAllLocalDomains
  exact ⟨h.compactSpace, h.t2Space⟩

/-- The point of the recognized localized pullback uses the compact
shrunk space for the recognized cospan. -/
theorem isCompactSpace_recognizedLocalizedPullback
    (hpush : PresentedAffinoidAlgebra.AffinoidPushout.FiniteBanachPushoutStatement K)
    (hf : strongEtale f)
    (hA : IsCompactSpace (localizationFunctor.obj A))
    (hB : IsCompactSpace (localizationFunctor.obj B))
    (hC : T2Space C.presentation.space) :
    IsCompactSpace (recognizedLocalizedPullback f g hpush hf).1.pt := by
  have hA' := hA.of_iso (recognitionSourceIso f)
  have hB' := hB.of_iso (recognitionSourceIso g)
  let : CompactSpace (recognitionSource f).presentation.space := hA'.1
  let : CompactSpace (recognitionSource g).presentation.space := hB'.1
  let : T2Space (recognitionSource f).presentation.space := hA'.2
  let : T2Space (recognitionSource g).presentation.space := hB'.2
  let : T2Space (localizedSpaceFunctor.obj (localizationFunctor.obj C)) := hC
  let e : C.presentation.space ≃ₜ (recognitionBase C).presentation.space :=
    TopCat.homeoOfIso (localizedSpaceFunctor.mapIso (recognitionBaseIso C))
  let : T2Space (recognitionBase C).presentation.space := e.t2Space
  let := recognition_fibreProductSpace_small f g hpush hf
  exact isCompactSpace_localization_smallFibreProduct (recognitionMap f) (recognitionMap g)

end Strong

/-- A pullback cone in the localized analytic category with a compact
Hausdorff point and the full universal property. -/
structure CompactLocalizedPullbackData
    {A B X : LocalizedCategory.{u, v, v} (K := K)} (f : A ⟶ X) (g : B ⟶ X) where
  cone : PullbackCone f g
  isLimit : IsLimit cone
  compact : IsCompactSpace cone.pt

/-- Pull back an étale arrow with compact Hausdorff source along an arrow
with compact Hausdorff source to the same Hausdorff base. -/
def compactLocalizedEtalePullback
    {A B X : LocalizedCategory.{u, v, v} (K := K)} (f : A ⟶ X) (g : B ⟶ X)
    (hf : etale f) (hA : IsCompactSpace A) (hB : IsCompactSpace B)
    (hX : T2Space (localizedSpaceFunctor.obj X)) :
    CompactLocalizedPullbackData f g := Classical.choice (show
    Nonempty (CompactLocalizedPullbackData f g) from by
  obtain ⟨A', h⟩ := localizedObjectEquiv.surjective A
  change localizationFunctor.obj A' = A at h
  subst A
  obtain ⟨B', h⟩ := localizedObjectEquiv.surjective B
  change localizationFunctor.obj B' = B at h
  subst B
  obtain ⟨X', h⟩ := localizedObjectEquiv.surjective X
  change localizationFunctor.obj X' = X at h
  subst X
  obtain ⟨φ, rfl⟩ := exists_localizedRightFraction f
  obtain ⟨ψ, rfl⟩ := exists_localizedRightFraction g
  let eA := localizedQuasiIso φ.s φ.hs
  let eB := localizedQuasiIso ψ.s ψ.hs
  let : IsIso (localizationFunctor.map φ.s) := eA.isIso_hom
  have hφ : strongEtale φ.f := by
    apply (etale_localizationFunctor_map_iff_strongEtale φ.f).mp
    rw [← localizationFunctor_map_s_comp_localizedRightFraction φ]
    exact etale_comp (etale_of_isIso _) hf
  let c := recognizedLocalizedPullback φ.f ψ.f AffinoidPushout.finiteBanachPushout hφ
  have hc : IsCompactSpace c.1.pt :=
    isCompactSpace_recognizedLocalizedPullback φ.f ψ.f AffinoidPushout.finiteBanachPushout
      hφ (hA.of_iso eA.symm) (hB.of_iso eB.symm) hX
  let p := c.1.fst ≫ eA.hom
  let q := c.1.snd ≫ eB.hom
  have hp : IsPullback p q (localizedRightFraction φ) (localizedRightFraction ψ) := by
    apply (IsPullback.of_isLimit c.2).of_iso (Iso.refl _) eA eB (Iso.refl _)
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
  exact ⟨⟨PullbackCone.mk p q hp.w, hp.isLimit, hc⟩⟩)

end Langlands.Analytic.SaturatedAtlasPresentation
