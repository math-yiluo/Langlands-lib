import Langlands.AlgebraicGeometry.ProjectiveBundle.LocalFrame

/-! # Actual evaluation sections in local frame coordinates -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules

universe u

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LocalFrame

variable {S : Scheme.{u}} {M N : S.Modules} {n : ℕ} {U V W T : S.Opens}

/-- The actual basis section on any open contained in the frame's domain. -/
def basisSection (e : LocalFrame M n U) (W : S.Opens) (h : W ≤ U)
    (i : Fin (n + 1)) : Γ(M, W) :=
  (e.coordinates W h).symm (Pi.single i 1)

lemma basisSection_eq (e : LocalFrame M n U) (h : W ≤ U) (i : Fin (n + 1)) :
    e.basisSection W h i =
      (show Γ(M, W) from (localBasisSection e ⟨i⟩).val (op (Over.mk (homOfLE h)))) :=
  e.coordinates_symm_single h i

/-- Restricting an actual basis section restricts its frame coordinates. -/
lemma basisSection_restrict (e : LocalFrame M n U) (hTW : T ≤ W) (hWU : W ≤ U)
    (i : Fin (n + 1)) :
    M.presheaf.map (homOfLE hTW).op (e.basisSection W hWU i) =
      e.basisSection T (hTW.trans hWU) i :=
  e.coordinates_symm_single_restrict hTW hWU i

/-- Coordinates for the dual frame evaluate on the original basis sections. -/
lemma dual_basisCoordinate (e : LocalFrame M n U) (i : Fin (n + 1)) :
    localBasisCoordinate e.dual ⟨i⟩ = localDualEvaluation (localBasisSection e ⟨i⟩) := by
  apply (cancel_epi e.dual.hom).mp
  dsimp only [localBasisCoordinate]
  rw [Iso.hom_inv_id_assoc]
  exact (dualLocalFreeHom_evaluation e ⟨i⟩).symm

/-- The dual-frame coordinate of a functional is its value on the primal basis. -/
lemma dual_coordinates (e : LocalFrame M n U) (h : W ≤ U)
    (σ : Γ(Langlands.Scheme.Modules.dual M, W)) (i : Fin (n + 1)) :
    e.dual.coordinates W h σ i = dualEval M W σ (e.basisSection W h i) := by
  rw [coordinates_apply, dual_basisCoordinate, basisSection_eq]
  rfl

/-- A dual basis section is the restricted primal coordinate functional. -/
lemma dual_basisSection (e : LocalFrame M n U) (h : W ≤ U) (i : Fin (n + 1)) :
    e.dual.basisSection W h i =
      LocalHom.restrict (homOfLE h) (localBasisCoordinate e ⟨i⟩) := by
  rw [basisSection_eq]
  change (dualLocalFreeIso e).hom.val.app (op (Over.mk (homOfLE h)))
      ((SheafOfModules.freeSection ⟨i⟩).val (op (Over.mk (homOfLE h)))) = _
  exact dualLocalFreeIso_basis e ⟨i⟩ (Over.mk (homOfLE h))

/-- Each row of the dual-frame change consists of primal basis-change coefficients. -/
lemma dual_change_coefficient (e : LocalFrame M n U) (f : LocalFrame M n V)
    (hWU : W ≤ U) (hWV : W ≤ V) (i j : Fin (n + 1)) :
    e.dual.change f.dual W hWU hWV (Pi.single j 1) i =
      e.coordinates W hWU (f.basisSection W hWV i) j := by
  change f.dual.coordinates W hWV (e.dual.basisSection W hWU j) i = _
  rw [dual_coordinates, dual_basisSection]
  rfl

/-- Primal basis sections transform by the rows of the actual dual-frame change. -/
lemma basisSection_change (e : LocalFrame M n U) (f : LocalFrame M n V)
    (hWU : W ≤ U) (hWV : W ≤ V) (i : Fin (n + 1)) :
    f.basisSection W hWV i =
      ∑ j : Fin (n + 1), e.dual.change f.dual W hWU hWV (Pi.single j 1) i •
        e.basisSection W hWU j := by
  simp_rw [dual_change_coefficient, basisSection_eq]
  exact ((e.coordinates W hWU).symm_apply_apply _).symm

/-- Evaluating a frame basis through an actual module-sheaf morphism. -/
def evaluatedSections (e : LocalFrame M n U) (ev : M ⟶ N) (W : S.Opens)
    (h : W ≤ U) (i : Fin (n + 1)) : Γ(N, W) :=
  ev.app W (e.basisSection W h i)

/-- Actual evaluated frame sections commute with restriction. -/
lemma evaluatedSections_restrict (e : LocalFrame M n U) (ev : M ⟶ N)
    (hTW : T ≤ W) (hWU : W ≤ U) (i : Fin (n + 1)) :
    N.presheaf.map (homOfLE hTW).op (e.evaluatedSections ev W hWU i) =
      e.evaluatedSections ev T (hTW.trans hWU) i := by
  dsimp only [evaluatedSections]
  change N.val.map (homOfLE hTW).op
      (ev.val.app (op W) (e.basisSection W hWU i)) =
    ev.val.app (op T) (e.basisSection T (hTW.trans hWU) i)
  exact (PresheafOfModules.naturality_apply ev.val (homOfLE hTW).op _).symm.trans
    (congrArg (ev.val.app (op T)) (e.basisSection_restrict hTW hWU i))

/-- The sections obtained by evaluation obey the dual-frame row-coordinate law. -/
lemma evaluatedSections_change (e : LocalFrame M n U) (f : LocalFrame M n V)
    (ev : M ⟶ N) (hWU : W ≤ U) (hWV : W ≤ V) (i : Fin (n + 1)) :
    f.evaluatedSections ev W hWV i =
      ∑ j : Fin (n + 1), e.dual.change f.dual W hWU hWV (Pi.single j 1) i •
        e.evaluatedSections ev W hWU j := by
  dsimp only [evaluatedSections]
  rw [basisSection_change e f hWU hWV i, map_sum]
  simp only [Scheme.Modules.Hom.app_smul]

end LocalFrame

section Pushforward

variable {X S : Scheme.{u}} {M : S.Modules} {N : X.Modules} {n : ℕ}
    {U V W : S.Opens} (p : X ⟶ S)
    (ev : M ⟶ (Scheme.Modules.pushforward p).obj N)

/-- Evaluate a genuine base frame to actual sections over the inverse-image open. -/
def evaluationSections (e : LocalFrame M n U) (W : S.Opens) (h : W ≤ U)
    (i : Fin (n + 1)) : Γ(N, p ⁻¹ᵁ W) :=
  e.evaluatedSections ev W h i

/-- For a scheme-theoretic evaluation, coefficients act through the actual
structure-sheaf map on the inverse-image open. -/
lemma evaluationSections_change (e : LocalFrame M n U) (f : LocalFrame M n V)
    (hWU : W ≤ U) (hWV : W ≤ V) (i : Fin (n + 1)) :
    evaluationSections p ev f W hWV i =
      ∑ j : Fin (n + 1),
        p.app W (e.dual.change f.dual W hWU hWV (Pi.single j 1) i) •
          evaluationSections p ev e W hWU j :=
  e.evaluatedSections_change f ev hWU hWV i

end Pushforward

end Langlands.AlgebraicGeometry.ProjectiveBundle
