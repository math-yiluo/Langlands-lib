import Langlands.GroupTheory.CocycleExtension
import Mathlib.Algebra.Ring.Units
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.GroupExtension.Defs
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-! # The lattice sign-cocycle extension -/

namespace Langlands.Covering.BrylinskiDeligne

open NormalizedTwoCocycle
open scoped commutatorElement

universe u v

variable (F : Type u) [Field F] {Y : Type v} [AddCommGroup Y]

local instance signCoefficientAction : MulDistribMulAction (Multiplicative Y) Fˣ where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

/-- An even integer power of the sign is the identity unit. -/
theorem negOne_zpow_even {n : ℤ} (hn : Even n) : (-1 : Fˣ) ^ n = 1 := by
  obtain ⟨m, rfl⟩ := hn
  rw [zpow_add, ← mul_zpow, neg_mul_neg, one_mul, one_zpow]

variable (D : LinearMap.BilinForm ℤ Y)

/-- The normalized cocycle of a bilinear form with the trivial action on units. -/
def latticeSignCocycle : NormalizedTwoCocycle (Multiplicative Y) Fˣ where
  toFun x := (-1 : Fˣ) ^ D x.1.toAdd x.2.toAdd
  normalized := by
    change (-1 : Fˣ) ^ D 0 0 = 1
    simp
  cocycle x y z := by
    change (-1 : Fˣ) ^ D (x.toAdd + y.toAdd) z.toAdd * (-1 : Fˣ) ^ D x.toAdd y.toAdd =
      (-1 : Fˣ) ^ D y.toAdd z.toAdd * (-1 : Fˣ) ^ D x.toAdd (y.toAdd + z.toAdd)
    simp only [map_add, LinearMap.add_apply, ← zpow_add]
    congr 1
    ac_rfl

/-- The group on lattice coordinates and units twisted by the sign cocycle. -/
abbrev LatticeSignExtension : Type (max u v) :=
  (latticeSignCocycle F D).Extension

namespace LatticeSignExtension

/-- A point with lattice coordinate `y` and coefficient `a`. -/
def mk (y : Y) (a : Fˣ) : LatticeSignExtension F D :=
  ⟨a, Multiplicative.ofAdd y⟩

@[simp] theorem mk_left (y : Y) (a : Fˣ) : (mk F D y a).left = a := rfl

@[simp] theorem mk_right (y : Y) (a : Fˣ) :
    (mk F D y a).right = Multiplicative.ofAdd y := rfl

@[simp] theorem mk_one : mk F D 0 1 = 1 := rfl

@[simp] theorem mk_right_left (x : LatticeSignExtension F D) :
    mk F D x.right.toAdd x.left = x := rfl

/-- The product in lattice and unit coordinates. -/
theorem mk_mul (y z : Y) (a b : Fˣ) :
    mk F D y a * mk F D z b = mk F D (y + z) (a * b * (-1 : Fˣ) ^ D y z) := rfl

/-- The short exact sequence associated to the sign cocycle. -/
def groupExtension : GroupExtension Fˣ (LatticeSignExtension F D) (Multiplicative Y) where
  inl := Extension.inl (latticeSignCocycle F D)
  rightHom := Extension.projection (latticeSignCocycle F D)
  inl_injective := Extension.inl_injective _
  rightHom_surjective := Extension.projection_surjective _
  range_inl_eq_ker_rightHom := Extension.range_inl_eq_ker_projection _

@[simp] theorem inl_eq_mk (a : Fˣ) : (groupExtension F D).inl a = mk F D 0 a := rfl

@[simp] theorem rightHom_apply (x : LatticeSignExtension F D) :
    (groupExtension F D).rightHom x = x.right := rfl

/-- The coefficient group lies in the center of the sign extension. -/
theorem central : (groupExtension F D).inl.range ≤ Subgroup.center (LatticeSignExtension F D) := by
  rintro _ ⟨a, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro x
  exact Extension.mul_inl (latticeSignCocycle F D) x a

/-- The group commutator `x * y * x⁻¹ * y⁻¹` is the sign of the sum of both bilinear values. -/
theorem commutator (x y : LatticeSignExtension F D) :
    ⁅x, y⁆ = (groupExtension F D).inl
      ((-1 : Fˣ) ^ (D ((groupExtension F D).rightHom x).toAdd
        ((groupExtension F D).rightHom y).toAdd +
        D ((groupExtension F D).rightHom y).toAdd ((groupExtension F D).rightHom x).toAdd)) := by
  let y₁ := x.right.toAdd
  let y₂ := y.right.toAdd
  let a := (-1 : Fˣ) ^ (D y₁ y₂ + D y₂ y₁)
  change ⁅x, y⁆ = (groupExtension F D).inl a
  have h : x * y = (groupExtension F D).inl a * (y * x) := by
    change mk F D y₁ x.left * mk F D y₂ y.left =
      mk F D 0 a * (mk F D y₂ y.left * mk F D y₁ x.left)
    simp only [mk_mul, zero_add, add_comm y₂ y₁, map_zero, LinearMap.zero_apply, zpow_zero, mul_one]
    congr 1
    dsimp only [a]
    rw [zpow_add]
    have hs : (-1 : Fˣ) ^ D y₂ y₁ * (-1 : Fˣ) ^ D y₂ y₁ = 1 := by
      rw [← zpow_add, negOne_zpow_even F ⟨D y₂ y₁, rfl⟩]
    calc
      _ = x.left * y.left * (-1 : Fˣ) ^ D y₁ y₂ := rfl
      _ = x.left * y.left * (-1 : Fˣ) ^ D y₁ y₂ *
          ((-1 : Fˣ) ^ D y₂ y₁ * (-1 : Fˣ) ^ D y₂ y₁) := by rw [hs, mul_one]
      _ = _ := by ac_rfl
  rw [commutatorElement_def, h]
  simp [mul_assoc]

end LatticeSignExtension

end Langlands.Covering.BrylinskiDeligne
