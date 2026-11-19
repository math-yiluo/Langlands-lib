import Langlands.Geometry.FormalGroup.ScalarTatePoints
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Scalar-power reductions of compatible torsion points -/

noncomputable section
universe u v

namespace Langlands.FormalGroup.ModuleLaw.scalarTatePoints
open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]
variable {M : ModuleLaw O R σ} {π : O} {A B : CommAlgCat.{v} R}

private theorem transition_val {m n : ℕ} (h : m ≤ n)
    (x : (M.scalarHom (π ^ n)).kernelPoints A) :
    (M.torsionTransitionLinear π h A x).val = π ^ (n - m) • x.val :=
  M.torsionTransition_app_val π h x

/-- Compatibility written in the original formal module point group. -/
theorem eval_val_eq_smul (x : M.scalarTatePoints π A) {m n : ℕ} (h : m ≤ n) :
    (eval m x).val = π ^ (n - m) • (eval n x).val := by
  rw [← transition_val h, transition_eval]

/-- Multiplication by each power of the scalar is injective on the compatible families. -/
theorem pow_smul_injective (n : ℕ) :
    Function.Injective (fun x : M.scalarTatePoints π A => π ^ n • x) := by
  intro x y hxy
  apply ext
  intro i
  apply Subtype.ext
  have hx := eval_val_eq_smul x (show i ≤ n + i by omega)
  have hy := eval_val_eq_smul y (show i ≤ n + i by omega)
  have he : n + i - i = n := Nat.add_sub_cancel_right n i
  rw [he] at hx hy
  rw [hx, hy]
  have h := congrArg (fun z => (eval (n + i) z).val) hxy
  change (eval (n + i) (π ^ n • x)).val = (eval (n + i) (π ^ n • y)).val at h
  rw [map_smul, map_smul] at h
  exact h

/-- If the n-th projection vanishes, shift the indices by n and view each shifted
point in the smaller kernel. This divides the family by the scalar power. -/
def dividePow (n : ℕ) (x : M.scalarTatePoints π A) (hx : eval n x = 0) :
    M.scalarTatePoints π A := by
  let y (i : ℕ) : (M.scalarHom (π ^ i)).kernelPoints A :=
    ⟨(eval (n + i) x).val, (M.mem_scalarKernel (π ^ i) A _).mpr (by
      have h := eval_val_eq_smul x (show n ≤ n + i by omega)
      rw [Nat.add_sub_cancel_left, hx] at h
      exact h.symm)⟩
  refine ⟨y, ?_⟩
  intro i j hij
  apply Subtype.ext
  rw [transition_val]
  change π ^ (j - i) • (eval (n + j) x).val = (eval (n + i) x).val
  have h := eval_val_eq_smul x (Nat.add_le_add_left hij n)
  have he : n + j - (n + i) = j - i := by omega
  rw [he] at h
  exact h.symm

@[simp]
theorem eval_dividePow_val (n : ℕ) (x : M.scalarTatePoints π A) (hx : eval n x = 0) (i : ℕ) :
    (eval i (dividePow n x hx)).val = (eval (n + i) x).val := rfl

@[simp]
theorem pow_smul_dividePow (n : ℕ) (x : M.scalarTatePoints π A) (hx : eval n x = 0) :
    π ^ n • dividePow n x hx = x := by
  apply ext
  intro i
  apply Subtype.ext
  rw [map_smul]
  change π ^ n • (eval i (dividePow n x hx)).val = (eval i x).val
  rw [eval_dividePow_val]
  have h := eval_val_eq_smul x (show i ≤ n + i by omega)
  rw [Nat.add_sub_cancel_right] at h
  exact h.symm

/-- The submodule of scalar-power multiples in the actual inverse limit. -/
def scalarPowerMultiples (n : ℕ) : Submodule O (M.scalarTatePoints π A) :=
  LinearMap.range (π ^ n • (LinearMap.id : M.scalarTatePoints π A →ₗ[O] M.scalarTatePoints π A))

/-- The kernel of the n-th projection is exactly the scalar-power multiples. -/
theorem ker_eval_eq_scalarPowerMultiples (n : ℕ) :
    (eval (M := M) (π := π) (A := A) n).ker = scalarPowerMultiples n := by
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    exact ⟨dividePow n x hx, pow_smul_dividePow n x hx⟩
  · rintro ⟨y, rfl⟩
    change eval n (π ^ n • y) = 0
    rw [map_smul]
    apply Subtype.ext
    change π ^ n • (eval n y).val = 0
    exact (M.mem_scalarKernel (π ^ n) A _).mp (eval n y).property

/-- The affine compatible-family module modulo the n-th scalar power. -/
abbrev ModScalarPower (n : ℕ) :=
  M.scalarTatePoints π A ⧸ scalarPowerMultiples (M := M) (π := π) (A := A) n

/-- The quotient modulo the scalar power is the actual image in the n-th torsion kernel. -/
def modScalarPowerEquivRange (n : ℕ) :
    ModScalarPower (M := M) (π := π) (A := A) n ≃ₗ[O]
      (eval (M := M) (π := π) (A := A) n).range :=
  (Submodule.quotEquivOfEq _ _ (ker_eval_eq_scalarPowerMultiples n).symm).trans
    (eval n).quotKerEquivRange

@[simp]
theorem modScalarPowerEquivRange_mk (n : ℕ) (x : M.scalarTatePoints π A) :
    (modScalarPowerEquivRange n (Submodule.Quotient.mk x)).val = eval n x := by
  change ((eval n).quotKerEquivRange
    (Submodule.quotEquivOfEq _ _ (ker_eval_eq_scalarPowerMultiples n).symm
      (Submodule.Quotient.mk x))).val = _
  rw [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivRange_apply_mk]

/-- Coefficient maps descend to the quotients by scalar-power multiples. -/
def modScalarPowerMapAlgebra (n : ℕ) (φ : A ⟶ B) :
    ModScalarPower (M := M) (π := π) (A := A) n →ₗ[O]
      ModScalarPower (M := M) (π := π) (A := B) n :=
  Submodule.mapQ _ _ (mapAlgebra φ) (by
    rintro _ ⟨x, rfl⟩
    refine ⟨mapAlgebra φ x, ?_⟩
    change π ^ n • mapAlgebra φ x = mapAlgebra φ (π ^ n • x)
    rw [map_smul])

@[simp]
theorem modScalarPowerMapAlgebra_mk (n : ℕ) (φ : A ⟶ B) (x : M.scalarTatePoints π A) :
    modScalarPowerMapAlgebra n φ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (mapAlgebra φ x) := rfl

/-- The evaluation image comparison commutes with actual kernel maps on test algebras. -/
theorem modScalarPowerEquivRange_mapAlgebra_val (n : ℕ) (φ : A ⟶ B)
    (x : ModScalarPower (M := M) (π := π) (A := A) n) :
    (modScalarPowerEquivRange n (modScalarPowerMapAlgebra n φ x)).val =
      (M.scalarHom (π ^ n)).kernelMap φ (modScalarPowerEquivRange n x).val := by
  induction x using Submodule.Quotient.induction_on with
  | _ y => simp only [modScalarPowerMapAlgebra_mk, modScalarPowerEquivRange_mk, eval_mapAlgebra]

end Langlands.FormalGroup.ModuleLaw.scalarTatePoints
