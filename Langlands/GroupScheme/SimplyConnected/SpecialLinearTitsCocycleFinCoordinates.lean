import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleReindex
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Finite coordinates of the special-linear diagonal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearTitsCocycle

/-- The first `n` indices are precisely the indices other than the last pivot. -/
def lastPivotEquiv (n : ℕ) :
    ULift.{u} (Fin n) ≃ ULift.{u} (SpecialLinear.OffPivot (Fin.last n)) :=
  (Equiv.ulift.trans (finSuccAboveEquiv (Fin.last n))).trans Equiv.ulift.symm

@[simp] theorem lastPivotEquiv_apply (n : ℕ) (c : ULift.{u} (Fin n)) :
    lastPivotEquiv n c = ⟨⟨c.down.castSucc, Fin.castSucc_ne_last c.down⟩⟩ := by
  apply ULift.ext
  apply Subtype.ext
  exact congrFun Fin.succAbove_last c.down

/-- The last-pivot weight has the usual first-`n` finite coordinates. -/
theorem weightCoord_lastPivotEquiv (n : ℕ) (x : Fin (n + 1)) (c : ULift.{u} (Fin n)) :
    SpecialLinear.weightCoord (Fin.last n) x (lastPivotEquiv n c).down =
      (if x = c.down.castSucc then 1 else 0) - (if x = Fin.last n then 1 else 0) := by
  rw [lastPivotEquiv_apply]
  by_cases hx : x = Fin.last n
  · subst x
    simp [Ne.symm (Fin.castSucc_ne_last c.down)]
  · rw [SpecialLinear.weightCoord_of_ne _ hx, Pi.single_apply]
    by_cases hxc : x = c.down.castSucc
    · subst x
      simp [Fin.castSucc_ne_last c.down]
    · simp [hx, hxc, Ne.symm hxc, Subtype.ext_iff]

/-- The actual isomorphism between the finite and last-pivot diagonal coordinates. -/
def lastPivotTorusIso (n : ℕ) (S : Scheme.{u}) :
    splitTorus.commGroupScheme S (ULift.{u} (Fin n)) ≅
      splitTorus.commGroupScheme S (ULift.{u} (SpecialLinear.OffPivot (Fin.last n))) :=
  splitTorus.commReindexIso S (lastPivotEquiv n)

variable (n : ℕ) (k : Type u) [Field k]

/-- Pulling back a diagonal-entry character gives its explicit finite exponent vector. -/
theorem lastPivotTorusIso_hom_comp_diagonalWeight (x : Fin (n + 1)) :
    (lastPivotTorusIso n (Spec (CommRingCat.of k))).hom ≫
        SpecialLinear.diagonalWeight (Fin.last n) (Spec (CommRingCat.of k)) x =
      (GeneralLinear.characterCoordEquiv (Fin n) k).symm
        (fun c => (if x = c.castSucc then 1 else 0) -
          (if x = Fin.last n then 1 else 0)) := by
  rw [lastPivotTorusIso, SpecialLinear.diagonalWeight_eq_characterLatticeEquiv_symm,
    splitTorus.commReindexIso_hom_comp_character]
  apply (GeneralLinear.characterCoordEquiv (Fin n) k).injective
  rw [LinearEquiv.apply_symm_apply]
  funext c
  rw [GeneralLinear.characterCoordEquiv_apply, AddEquiv.apply_symm_apply]
  exact weightCoord_lastPivotEquiv.{u} n x ⟨c⟩

/-- Pullback preserves the differences giving the finite root characters. -/
theorem lastPivotTorusIso_hom_comp_diagonalWeight_sub (x y : Fin (n + 1)) :
    (lastPivotTorusIso n (Spec (CommRingCat.of k))).hom ≫
        (SpecialLinear.diagonalWeight (Fin.last n) (Spec (CommRingCat.of k)) x -
          SpecialLinear.diagonalWeight (Fin.last n) (Spec (CommRingCat.of k)) y) =
      (GeneralLinear.characterCoordEquiv (Fin n) k).symm
        ((fun c => (if x = c.castSucc then 1 else 0) -
            (if x = Fin.last n then 1 else 0)) -
          (fun c => (if y = c.castSucc then 1 else 0) -
            (if y = Fin.last n then 1 else 0))) := by
  rw [Preadditive.comp_sub, lastPivotTorusIso_hom_comp_diagonalWeight,
    lastPivotTorusIso_hom_comp_diagonalWeight, map_sub]

end Langlands.GroupScheme.SpecialLinearTitsCocycle
