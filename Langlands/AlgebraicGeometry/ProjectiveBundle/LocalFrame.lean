import Langlands.AlgebraicGeometry.ModuleDualLocalFree
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.GlobalLinearAction

/-! # Coordinates of genuine local frames -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules

universe u

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} (M : S.Modules) (n : ℕ)

/-- A frame is an actual isomorphism of module sheaves on the slice over an open. -/
abbrev LocalFrame (U : S.Opens) :=
  SheafOfModules.free (R := S.ringCatSheaf.over U) (ULift.{u} (Fin (n + 1))) ≅ M.over U

namespace LocalFrame

variable {M n} {U V W : S.Opens}

/-- Restrict a genuine frame to any smaller open. -/
def restrict (e : LocalFrame M n U) (h : V ≤ U) : LocalFrame M n V :=
  SheafOfModules.mapFreeIso (SheafOfModules.overMap S.ringCatSheaf (homOfLE h))
      (ULift.{u} (Fin (n + 1)))
      (SheafOfModules.overMapUnitIso (homOfLE h)).symm ≪≫
    (SheafOfModules.overMap S.ringCatSheaf (homOfLE h)).mapIso e ≪≫
    (SheafOfModules.overFunctorMap S.ringCatSheaf (homOfLE h)).app M

/-- The coordinate equivalence on every open contained in the frame's domain. -/
def coordinates (e : LocalFrame M n U) (V : S.Opens) (h : V ≤ U) :
    Γ(M, V) ≃ₗ[Γ(S, V)] (Fin (n + 1) → Γ(S, V)) := by
  classical
  exact
    { toFun := fun x i => LocalHom.app (localBasisCoordinate e ⟨i⟩) (homOfLE h) x
      invFun := fun a => ∑ i : Fin (n + 1), a i •
        (show Γ(M, V) from (localBasisSection e ⟨i⟩).val (op (Over.mk (homOfLE h))))
      left_inv := by
        intro x
        exact (Fintype.sum_equiv
          (Equiv.ulift.symm : Fin (n + 1) ≃ ULift.{u} (Fin (n + 1)))
          _ _ (fun i => rfl)).trans (localBasis_expansion e (Over.mk (homOfLE h)) x)
      right_inv := by
        intro a
        funext i
        change (LocalHom.app (localBasisCoordinate e ⟨i⟩) (homOfLE h)).hom
          (∑ j : Fin (n + 1), a j • (show Γ(M, V) from
            (localBasisSection e ⟨j⟩).val (op (Over.mk (homOfLE h))))) = a i
        rw [map_sum]
        calc
          _ = ∑ j : Fin (n + 1), a j * (if j = i then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [LinearMap.map_smul]
            change a j * _ = _
            simpa using congrArg (fun t : Γ(S, V) => a j * t)
              (localBasisCoordinate_basis e ⟨i⟩ ⟨j⟩ (Over.mk (homOfLE h)))
          _ = a i := by simp
      map_add' := by
        intro x y
        funext i
        exact map_add _ _ _
      map_smul' := by
        intro r x
        funext i
        exact (LocalHom.app (localBasisCoordinate e ⟨i⟩) (homOfLE h)).hom.map_smul r x }

@[simp]
lemma coordinates_apply (e : LocalFrame M n U) (h : V ≤ U) (x : Γ(M, V))
    (i : Fin (n + 1)) :
    e.coordinates V h x i =
      LocalHom.app (localBasisCoordinate e ⟨i⟩) (homOfLE h) x := rfl

/-- The inverse coordinate map takes a standard vector to the corresponding basis section. -/
lemma coordinates_symm_single (e : LocalFrame M n U) (h : V ≤ U) (i : Fin (n + 1)) :
    (e.coordinates V h).symm (Pi.single i 1) =
      (show Γ(M, V) from (localBasisSection e ⟨i⟩).val (op (Over.mk (homOfLE h)))) := by
  classical
  apply (e.coordinates V h).injective
  rw [LinearEquiv.apply_symm_apply]
  funext j
  simp only [coordinates_apply, Pi.single_apply]
  simpa [eq_comm] using
    (localBasisCoordinate_basis e ⟨j⟩ ⟨i⟩ (Over.mk (homOfLE h))).symm

/-- Coordinates commute with restriction, including restriction of all coefficients. -/
lemma coordinates_restrict (e : LocalFrame M n U) (hWV : W ≤ V) (hVU : V ≤ U)
    (x : Γ(M, V)) (i : Fin (n + 1)) :
    e.coordinates W (hWV.trans hVU) (M.presheaf.map (homOfLE hWV).op x) i =
      S.presheaf.map (homOfLE hWV).op (e.coordinates V hVU x i) := by
  let k : Over.mk (homOfLE (hWV.trans hVU)) ⟶ Over.mk (homOfLE hVU) :=
    Over.homMk (homOfLE hWV)
  exact PresheafOfModules.naturality_apply (localBasisCoordinate e ⟨i⟩).val k.op x

/-- Restrictions of the inverse's standard vectors are the inverse's standard vectors. -/
lemma coordinates_symm_single_restrict (e : LocalFrame M n U)
    (hWV : W ≤ V) (hVU : V ≤ U) (i : Fin (n + 1)) :
    M.presheaf.map (homOfLE hWV).op ((e.coordinates V hVU).symm (Pi.single i 1)) =
      (e.coordinates W (hWV.trans hVU)).symm (Pi.single i 1) := by
  rw [coordinates_symm_single, coordinates_symm_single]
  exact PresheafOfModules.sections_property (localBasisSection e ⟨i⟩)
    (Over.homMk (homOfLE hWV) :
      Over.mk (homOfLE (hWV.trans hVU)) ⟶ Over.mk (homOfLE hVU)).op

/-- The dual frame uses the original frame's actual coordinate functionals. -/
def dual (e : LocalFrame M n U) : LocalFrame (Langlands.Scheme.Modules.dual M) n U :=
  dualLocalFreeIso e

/-- Change between two frames on a common smaller open. -/
def change (e : LocalFrame M n U) (f : LocalFrame M n V)
    (W : S.Opens) (hWU : W ≤ U) (hWV : W ≤ V) :
    (Fin (n + 1) → Γ(S, W)) ≃ₗ[Γ(S, W)] (Fin (n + 1) → Γ(S, W)) :=
  (e.coordinates W hWU).symm.trans (f.coordinates W hWV)

@[simp]
lemma change_self (e : LocalFrame M n U) (h : W ≤ U) :
    e.change e W h h = LinearEquiv.refl Γ(S, W) _ := by
  apply LinearEquiv.ext
  intro x
  exact (e.coordinates W h).apply_symm_apply x

lemma change_trans {T : S.Opens} (e : LocalFrame M n U) (f : LocalFrame M n V)
    (g : LocalFrame M n T) (hWU : W ≤ U) (hWV : W ≤ V) (hWT : W ≤ T) :
    (e.change f W hWU hWV).trans (f.change g W hWV hWT) =
      e.change g W hWU hWT := by
  apply LinearEquiv.ext
  intro x
  exact congrArg (g.coordinates W hWT)
    ((f.coordinates W hWV).symm_apply_apply ((e.coordinates W hWU).symm x))

/-- Every entry of a frame change restricts by the structure-sheaf restriction map. -/
lemma change_restrict {T : S.Opens} (e : LocalFrame M n U) (f : LocalFrame M n V)
    (hTW : T ≤ W) (hWU : W ≤ U) (hWV : W ≤ V) :
    ProjectiveSpace.coordinateBaseChange n (S.presheaf.map (homOfLE hTW).op).hom
        (e.change f W hWU hWV) =
      e.change f T (hTW.trans hWU) (hTW.trans hWV) := by
  apply ProjectiveSpace.coordinateEquiv_ext
  intro i j
  rw [ProjectiveSpace.coordinateBaseChange_coeff]
  change S.presheaf.map (homOfLE hTW).op
      (f.coordinates W hWV ((e.coordinates W hWU).symm (Pi.single j 1)) i) =
    f.coordinates T (hTW.trans hWV)
      ((e.coordinates T (hTW.trans hWU)).symm (Pi.single j 1)) i
  rw [← coordinates_restrict, coordinates_symm_single_restrict]

end LocalFrame

end Langlands.AlgebraicGeometry.ProjectiveBundle
