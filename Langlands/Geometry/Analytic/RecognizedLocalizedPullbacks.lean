import Langlands.Geometry.Analytic.FibreProductLocalizedLimit
import Langlands.Geometry.Analytic.RecognitionFibreProductSmallness

/-! # Actual localized pullbacks from a strong etale leg -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B X : SaturatedAtlasPresentation.{u, v, v} K}
  (f : A ⟶ X) (g : B ⟶ X)

/-- Naturality of the complete recognition comparison, with the actual
localized inverses used to return to the original cospan. -/
theorem recognitionMap_localized_inverse_square :
    localizationFunctor.map (recognitionMap f) ≫ (recognitionBaseIso X).inv =
      (recognitionSourceIso f).inv ≫ localizationFunctor.map f := by
  apply (cancel_epi (recognitionSourceIso f).hom).mp
  rw [← Category.assoc, recognitionMap_localized_square]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- Construct a full limiting cone over the original mapped strong
cospan, in the original common space/index universe. Smallness is proved
from the strong etale input and finite Banach pushout theorem. -/
def recognizedLocalizedPullback
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K) (hf : strongEtale f) :
    Σ c : PullbackCone (localizationFunctor.map f) (localizationFunctor.map g), IsLimit c := by
  letI := recognition_fibreProductSpace_small f g hpush hf
  let F := recognitionMap f
  let G := recognitionMap g
  let p := localizationFunctor.map (smallFibreProductFst F G) ≫ (recognitionSourceIso f).inv
  let q := localizationFunctor.map (smallFibreProductSnd F G) ≫ (recognitionSourceIso g).inv
  have h : IsPullback p q (localizationFunctor.map f) (localizationFunctor.map g) := by
    apply (smallFibreProduct_isPullback F G).of_iso (Iso.refl _)
      (recognitionSourceIso f).symm (recognitionSourceIso g).symm (recognitionBaseIso X).symm
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
      rfl
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
      rfl
    · exact recognitionMap_localized_inverse_square f
    · exact recognitionMap_localized_inverse_square g
  exact ⟨PullbackCone.mk p q h.w, h.isLimit⟩

/-- The constructed pullback exists without any supplied size or atlas
adapter hypothesis, for the original mapped strong cospan. -/
theorem exists_localizedPullback_of_strongEtale
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K) (hf : strongEtale f) :
    ∃ (P : LocalizedCategory.{u, v, v} (K := K))
      (p : P ⟶ localizationFunctor.obj A) (q : P ⟶ localizationFunctor.obj B),
      IsPullback p q (localizationFunctor.map f) (localizationFunctor.map g) := by
  let c := recognizedLocalizedPullback f g hpush hf
  exact ⟨c.1.pt, c.1.fst, c.1.snd, IsPullback.of_isLimit c.2⟩

end Langlands.Analytic.SaturatedAtlasPresentation
