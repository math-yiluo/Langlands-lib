import Langlands.Global.NumberFieldAdeleLevelColimitStatement
import Langlands.Global.NumberFieldAdeleLevelTopologyProof
import Langlands.Global.FiniteAdeleLevelColimitProof

/-! # Categorical colimit proof for actual full number-field adelic levels -/

noncomputable section

universe u

open CategoryTheory Limits

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K]

def numberFieldAdeleLevelRingDesc (c : Cocone (numberFieldAdeleLevelRingDiagram K)) :
    Adeles K →+* c.pt :=
  SubringCover.desc (B := c.pt) (numberFieldAdeleLevel K)
    (fun _ _ h => numberFieldAdeleLevel_mono K h)
    (exists_mem_numberFieldAdeleLevel K) (fun S => (c.ι.app S).hom)
    (fun _S _T h => congrArg CommRingCat.Hom.hom (c.w (homOfLE h)))

theorem numberFieldAdeleLevelRingDesc_apply (c : Cocone (numberFieldAdeleLevelRingDiagram K))
    (S : Finset (FinitePlace K)) (a : numberFieldAdeleLevel K S) :
    numberFieldAdeleLevelRingDesc K c a.val = (c.ι.app S).hom a :=
  SubringCover.desc_apply _ _ _ _ _ S a

def numberFieldAdeleLevelRingIsColimit : IsColimit (numberFieldAdeleLevelRingCocone K) where
  desc c := CommRingCat.ofHom (numberFieldAdeleLevelRingDesc K c)
  fac c S := by
    ext a
    exact numberFieldAdeleLevelRingDesc_apply K c S a
  uniq c m hm := by
    ext a
    obtain ⟨S, ha⟩ := exists_mem_numberFieldAdeleLevel K a
    have h := congrArg (fun k => k.hom ⟨a, ha⟩) (hm S)
    exact h.trans (numberFieldAdeleLevelRingDesc_apply K c S ⟨a, ha⟩).symm

def numberFieldAdeleLevelIsColimit : IsColimit (numberFieldAdeleLevelCocone K) where
  desc c := by
    let f : Adeles K →+* c.pt :=
      numberFieldAdeleLevelRingDesc K ((forget₂ TopCommRingCat CommRingCat).mapCocone c)
    refine ⟨f, ?_⟩
    apply (continuous_iff_numberFieldAdeleLevel K (X := c.pt) f).mpr
    intro S
    have heq : (f ∘ (numberFieldAdeleLevel K S).subtype) =
        (c.ι.app S).val := by
      funext a
      exact numberFieldAdeleLevelRingDesc_apply K _ S a
    exact heq.symm ▸ (c.ι.app S).property
  fac c S := by
    apply Subtype.ext
    ext a
    exact numberFieldAdeleLevelRingDesc_apply K _ S a
  uniq c m hm := by
    apply Subtype.ext
    ext a
    obtain ⟨S, ha⟩ := exists_mem_numberFieldAdeleLevel K a
    have h := congrArg (fun k => k.val ⟨a, ha⟩) (hm S)
    exact h.trans (numberFieldAdeleLevelRingDesc_apply K
      ((forget₂ TopCommRingCat CommRingCat).mapCocone c) S ⟨a, ha⟩).symm

/-- Both exact categorical universal properties of the canonical level cocones. -/
theorem numberFieldAdeleLevelColimit : NumberFieldAdeleLevelColimitStatement.{u} := by
  intro K _ _
  exact ⟨⟨numberFieldAdeleLevelIsColimit K⟩, ⟨numberFieldAdeleLevelRingIsColimit K⟩⟩

end Langlands.Global
