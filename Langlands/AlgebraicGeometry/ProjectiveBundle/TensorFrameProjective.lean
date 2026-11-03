import Langlands.AlgebraicGeometry.ProjectiveBundle.TensorFrameCoordinates

/-! # Projective coordinate changes of tensor frames -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.RelativeProjectiveSpace

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

lemma coordinateBaseChange_smulOfUnit (n : ℕ)
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) (c : Rˣ) :
    coordinateBaseChange n φ (LinearEquiv.smulOfUnit c) =
      LinearEquiv.smulOfUnit (Units.map φ.toMonoidHom c) := by
  apply coordinateEquiv_ext n
  intro i j
  rw [coordinateBaseChange_coeff]
  change φ ((c : R) * (Pi.single j (1 : R) : Fin (n + 1) → R) i) =
    φ (c : R) * (Pi.single j (1 : A) : Fin (n + 1) → A) i
  rw [map_mul]
  congr 1
  classical
  by_cases h : j = i <;> simp [h]

end Langlands.AlgebraicGeometry.ProjectiveSpace

namespace Langlands.AlgebraicGeometry.ProjectiveBundle.LocalFrame

variable {S : Scheme.{u}} {M N : S.Modules} {n : ℕ} {U V W T : S.Opens}

/-- The actual projective scheme map given by a change of dual frames. -/
def projectiveChange (e : LocalFrame M n U) (f : LocalFrame M n V)
    (W : S.Opens) (hWU : W ≤ U) (hWV : W ≤ V) :
    RelativeProjectiveSpace W.toScheme n ⟶ RelativeProjectiveSpace W.toScheme n :=
  globalLinearAction n (coordinatesOnOpen n W (e.dual.change f.dual W hWU hWV))

@[simp]
lemma projectiveChange_self (e : LocalFrame M n U) (h : W ≤ U) :
    e.projectiveChange e W h h = 𝟙 _ := by
  dsimp only [projectiveChange, coordinatesOnOpen]
  rw [change_self, ProjectiveSpace.coordinateBaseChange_refl, globalLinearAction_refl]

lemma projectiveChange_comp (e : LocalFrame M n U) (f : LocalFrame M n V)
    (g : LocalFrame M n T) (hWU : W ≤ U) (hWV : W ≤ V) (hWT : W ≤ T) :
    e.projectiveChange f W hWU hWV ≫ f.projectiveChange g W hWV hWT =
      e.projectiveChange g W hWU hWT := by
  dsimp only [projectiveChange, coordinatesOnOpen]
  rw [globalLinearAction_comp, ← ProjectiveSpace.coordinateBaseChange_trans, change_trans]

lemma projectiveChange_restrict (e : LocalFrame M n U) (f : LocalFrame M n V)
    (hTW : T ≤ W) (hWU : W ≤ U) (hWV : W ≤ V) :
    RelativeProjectiveSpace.map n (S.homOfLE hTW) ≫ e.projectiveChange f W hWU hWV =
      e.projectiveChange f T (hTW.trans hWU) (hTW.trans hWV) ≫
        RelativeProjectiveSpace.map n (S.homOfLE hTW) := by
  dsimp only [projectiveChange]
  rw [map_globalLinearAction, coordinatesOnOpen_restrict, change_restrict]

lemma tensor_dual_change (e f : LocalFrame M n U)
    (t s : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (h : V ≤ U) :
    (e.tensor t).dual.change (f.tensor s).dual V h h =
      (e.dual.change f.dual V h h).trans
        (LinearEquiv.smulOfUnit
          (Units.map (S.presheaf.map (homOfLE h).op).hom.toMonoidHom
            (TensorFrames.trivializationUnit s t))) := by
  apply ProjectiveSpace.coordinateEquiv_ext n
  intro i j
  rw [tensor_dual_change_coefficient]
  rfl

/-- Tensoring by a line changes dual coordinate matrices only by a scalar unit,
so the actual projective scheme maps coincide. -/
lemma tensor_projectiveChange (e f : LocalFrame M n U)
    (t s : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (h : V ≤ U) :
    (e.tensor t).projectiveChange (f.tensor s) V h h =
      e.projectiveChange f V h h := by
  dsimp only [projectiveChange, coordinatesOnOpen]
  rw [tensor_dual_change, ProjectiveSpace.coordinateBaseChange_trans,
    ProjectiveSpace.coordinateBaseChange_smulOfUnit,
    ← globalLinearAction_comp, globalLinearAction_smulOfUnit, Category.comp_id]

end Langlands.AlgebraicGeometry.ProjectiveBundle.LocalFrame
