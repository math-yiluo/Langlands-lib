import Langlands.AlgebraicGeometry.Modules.TensorContractionTransport
import Langlands.AlgebraicGeometry.ProjectiveBundle.TensorFrameProjective

/-! # Tensor-frame comparison on arbitrary overlaps -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Modules
open Langlands.AlgebraicGeometry.RelativeProjectiveSpace

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Modules

variable {S : Scheme.{u}} {N : S.Modules} {U V W : S.Opens}

lemma lineSection_eq_coordinate_smul
    (t : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (h : W ≤ U) (x : Γ(N, W)) :
    x = lineCoordinates t W h x • lineBasisSection t W h := by
  apply (lineCoordinates t W h).injective
  rw [map_smul, lineCoordinates_lineBasisSection]
  exact (mul_one _).symm

lemma lineCoordinates_change_mul
    (t : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (s : N.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)
    (hWU : W ≤ U) (hWV : W ≤ V) (x : Γ(N, W)) :
    lineCoordinates s W hWV x =
      lineCoordinates s W hWV (lineBasisSection t W hWU) * lineCoordinates t W hWU x := by
  calc
    _ = lineCoordinates s W hWV
        (lineCoordinates t W hWU x • lineBasisSection t W hWU) :=
      congrArg (lineCoordinates s W hWV) (lineSection_eq_coordinate_smul t hWU x)
    _ = lineCoordinates t W hWU x •
        lineCoordinates s W hWV (lineBasisSection t W hWU) := map_smul _ _ _
    _ = _ := mul_comm _ _

/-- The unit comparing two actual line charts on a common original open. -/
def lineComparisonUnit
    (t : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (s : N.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)
    (W : S.Opens) (hWU : W ≤ U) (hWV : W ≤ V) : Γ(S, W)ˣ where
  val := lineCoordinates s W hWV (lineBasisSection t W hWU)
  inv := lineCoordinates t W hWU (lineBasisSection s W hWV)
  val_inv := by
    have hh := lineCoordinates_change_mul t s hWU hWV (lineBasisSection s W hWV)
    simpa only [lineCoordinates_lineBasisSection] using hh.symm
  inv_val := by
    have hh := lineCoordinates_change_mul s t hWV hWU (lineBasisSection t W hWU)
    simpa only [lineCoordinates_lineBasisSection] using hh.symm

lemma lineCoordinates_change
    (t : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (s : N.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)
    (hWU : W ≤ U) (hWV : W ≤ V) (x : Γ(N, W)) :
    lineCoordinates s W hWV x =
      (lineComparisonUnit t s W hWU hWV : Γ(S, W)) * lineCoordinates t W hWU x :=
  lineCoordinates_change_mul t s hWU hWV x

end Langlands.AlgebraicGeometry.Modules

namespace Langlands.AlgebraicGeometry.ProjectiveBundle.LocalFrame

variable {S : Scheme.{u}} {M N : S.Modules} {n : ℕ} {U V W : S.Opens}

lemma tensor_overlap_dual_change_coefficient (e : LocalFrame M n U) (f : LocalFrame M n V)
    (t : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (s : N.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)
    (hWU : W ≤ U) (hWV : W ≤ V) (i j : Fin (n + 1)) :
    (e.tensor t).dual.change (f.tensor s).dual W hWU hWV (Pi.single j 1) i =
      (lineComparisonUnit s t W hWV hWU : Γ(S, W)) *
        e.dual.change f.dual W hWU hWV (Pi.single j 1) i := by
  rw [dual_change_coefficient, dual_change_coefficient,
    tensor_coordinates, tensor_basisSection,
    modE_tensorRestrictionTrivialization_symm,
    modE_tensorRestrictionTrivialization_pureSection, map_smul]
  rfl

lemma tensor_overlap_dual_change (e : LocalFrame M n U) (f : LocalFrame M n V)
    (t : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (s : N.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)
    (hWU : W ≤ U) (hWV : W ≤ V) :
    (e.tensor t).dual.change (f.tensor s).dual W hWU hWV =
      (e.dual.change f.dual W hWU hWV).trans
        (LinearEquiv.smulOfUnit (lineComparisonUnit s t W hWV hWU)) := by
  apply ProjectiveSpace.coordinateEquiv_ext n
  intro i j
  rw [tensor_overlap_dual_change_coefficient]
  rfl

/-- Tensor-line scalar comparison cancels on the actual projective transition over any overlap. -/
lemma tensor_overlap_projectiveChange (e : LocalFrame M n U) (f : LocalFrame M n V)
    (t : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (s : N.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)
    (hWU : W ≤ U) (hWV : W ≤ V) :
    (e.tensor t).projectiveChange (f.tensor s) W hWU hWV =
      e.projectiveChange f W hWU hWV := by
  dsimp only [projectiveChange, coordinatesOnOpen]
  rw [tensor_overlap_dual_change, ProjectiveSpace.coordinateBaseChange_trans,
    ProjectiveSpace.coordinateBaseChange_smulOfUnit,
    ← globalLinearAction_comp, globalLinearAction_smulOfUnit, Category.comp_id]

end Langlands.AlgebraicGeometry.ProjectiveBundle.LocalFrame
