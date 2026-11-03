import Langlands.AlgebraicGeometry.Modules.TensorContractionSections

/-! # Tensor contraction on original opens -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules Langlands.SchemeModule.SectionClearing

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Modules

variable {S : Scheme.{u}} {M N : S.Modules} {U V : S.Opens}

/-- The unique section whose coordinate in the given line chart is one. -/
def lineBasisSection
    (t : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (V : S.Opens) (h : V ≤ U) : Γ(N, V) :=
  (lineCoordinates t V h).symm 1

@[simp]
lemma lineCoordinates_lineBasisSection
    (t : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (h : V ≤ U) :
    lineCoordinates t V h (lineBasisSection t V h) = 1 :=
  (lineCoordinates t V h).apply_symm_apply 1

lemma ofImage_pureSection (M N : S.Modules) (W : U.toScheme.Opens)
    (m : Γ(M, U.ι ''ᵁ W)) (n : Γ(N, U.ι ''ᵁ W)) :
    ofImage (tensorObj M N) (pureSection M N (U.ι ''ᵁ W) m n) =
      (restrictTensorHom U M N).app W
        (pureSection (M.restrict U.ι) (N.restrict U.ι) W
          (ofImage M m) (ofImage N n)) :=
  (restrictTensorHom_app_tmul U M N W (ofImage M m) (ofImage N n)).symm

lemma lineCoordinates_eq_chartE
    (t : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (h : V ≤ U) (x : Γ(N, V)) :
    lineCoordinates t V h x = chartE t V h x := by
  rw [lineCoordinates_eq_modE]
  rfl

/-- Contraction on any smaller original open evaluates pure sections by the line chart. -/
lemma modE_tensorRestrictionTrivialization_pureSection (M : S.Modules)
    (t : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (h : V ≤ U) (m : Γ(M, V)) (n : Γ(N, V)) :
    SerreVanishing.modE (tensorRestrictionTrivialization M N U t) V h
      (pureSection M N V m n) = lineCoordinates t V h n • m := by
  rw [lineCoordinates_eq_chartE]
  unfold SerreVanishing.modE chartE
  rw [pureSection_restrict, ofImage_pureSection,
    tensorRestrictionTrivialization_pureSection, SerreVanishing.toImage_smul,
    Scheme.Modules.map_smul]
  apply congrArg₂ (fun (a : Γ(S, V)) (x : Γ(M, V)) => a • x)
  · rfl
  · exact (modules_map_map M _ _ m).trans (modules_map_id M _ m)

/-- The inverse contraction inserts the section with line coordinate one. -/
lemma modE_tensorRestrictionTrivialization_symm (M : S.Modules)
    (t : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (h : V ≤ U) (m : Γ(M, V)) :
    SerreVanishing.modE (tensorRestrictionTrivialization M N U t).symm V h m =
      pureSection M N V m (lineBasisSection t V h) := by
  apply SerreVanishing.modE_injective (tensorRestrictionTrivialization M N U t) V h
  have hi := SerreVanishing.modE_symm_modE
    (tensorRestrictionTrivialization M N U t).symm V h m
  simp only [Iso.symm_symm_eq] at hi
  rw [hi, modE_tensorRestrictionTrivialization_pureSection]
  simp only [lineCoordinates_lineBasisSection, one_smul]

end Langlands.AlgebraicGeometry.Modules
