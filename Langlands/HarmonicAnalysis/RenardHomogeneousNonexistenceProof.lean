import Langlands.HarmonicAnalysis.RenardHomogeneousNonexistenceStatement
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# Renard II.3.9: untwisted invariant distributions need not exist (proof)

The witness is the group of affine maps `x ↦ 2 ^ n * x + b` of `ℚ_[2]`, on the
carrier `ℤ × ℚ_[2]` with the product topology, and the closed subgroup `H` of
its linear elements `(n, 0)`. The second coordinate identifies `H\G` with
`ℚ_[2]`, and right translation by `(1, 0)` becomes `x ↦ 2 * x`. It enlarges the
closed unit ball, so an invariant functional vanishes on a nonzero nonnegative
difference of two indicator functions, contradicting strict positivity.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis.HomogeneousFunctions.Renard

namespace Nonexistence

/-- The group of affine maps `x ↦ 2 ^ n * x + b` of `ℚ_[2]`, on the carrier
`ℤ × ℚ_[2]`. -/
def AffineTwo : Type := ℤ × ℚ_[2]

namespace AffineTwo

/-- The point `(n, b)`. -/
def mk (n : ℤ) (b : ℚ_[2]) : AffineTwo := (n, b)

/-- The exponent `n` of `(n, b)`. -/
def power (x : AffineTwo) : ℤ := Prod.fst (show ℤ × ℚ_[2] from x)

/-- The translation part `b` of `(n, b)`. -/
def offset (x : AffineTwo) : ℚ_[2] := Prod.snd (show ℤ × ℚ_[2] from x)

@[simp] theorem power_mk (n : ℤ) (b : ℚ_[2]) : power (mk n b) = n := rfl

@[simp] theorem offset_mk (n : ℤ) (b : ℚ_[2]) : offset (mk n b) = b := rfl

theorem ext' {x y : AffineTwo} (h₁ : power x = power y) (h₂ : offset x = offset y) :
    x = y :=
  Prod.ext h₁ h₂

/-- `(n, b) * (m, c) = (n + m, 2 ^ m * b + c)`: first `x ↦ 2 ^ n * x + b`,
then `x ↦ 2 ^ m * x + c`. -/
instance : Mul AffineTwo :=
  ⟨fun x y => mk (power x + power y) ((2 : ℚ_[2]) ^ power y * offset x + offset y)⟩

instance : One AffineTwo := ⟨mk 0 0⟩

instance : Inv AffineTwo :=
  ⟨fun x => mk (-power x) (-((2 : ℚ_[2]) ^ (-power x) * offset x))⟩

@[simp] theorem power_mul (x y : AffineTwo) : power (x * y) = power x + power y := rfl

@[simp] theorem offset_mul (x y : AffineTwo) :
    offset (x * y) = (2 : ℚ_[2]) ^ power y * offset x + offset y := rfl

@[simp] theorem power_one : power 1 = 0 := rfl

@[simp] theorem offset_one : offset 1 = 0 := rfl

@[simp] theorem power_inv (x : AffineTwo) : power x⁻¹ = -power x := rfl

@[simp] theorem offset_inv (x : AffineTwo) :
    offset x⁻¹ = -((2 : ℚ_[2]) ^ (-power x) * offset x) := rfl

theorem two_zpow_mul_neg (n : ℤ) : (2 : ℚ_[2]) ^ n * (2 : ℚ_[2]) ^ (-n) = 1 := by
  rw [← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero]

instance : Group AffineTwo :=
  Group.ofLeftAxioms
    (fun x y z => by
      apply ext'
      · simp [add_assoc]
      · simp only [offset_mul, power_mul]
        rw [zpow_add₀ two_ne_zero]
        ring)
    (fun x => ext' (by simp) (by simp))
    (fun x => ext' (by simp) (by
      simp only [offset_mul, offset_inv, offset_one]
      linear_combination (-offset x) * two_zpow_mul_neg (power x)))

/-- The product topology of `ℤ × ℚ_[2]`. -/
instance : TopologicalSpace AffineTwo := inferInstanceAs (TopologicalSpace (ℤ × ℚ_[2]))

instance : T2Space AffineTwo := inferInstanceAs (T2Space (ℤ × ℚ_[2]))

instance : LocallyCompactSpace AffineTwo := inferInstanceAs (LocallyCompactSpace (ℤ × ℚ_[2]))

instance : TotallyDisconnectedSpace AffineTwo :=
  inferInstanceAs (TotallyDisconnectedSpace (ℤ × ℚ_[2]))

theorem continuous_power : Continuous power :=
  continuous_fst (X := ℤ) (Y := ℚ_[2])

theorem continuous_offset : Continuous offset :=
  continuous_snd (X := ℤ) (Y := ℚ_[2])

theorem continuous_mk' {X : Type} [TopologicalSpace X] {f : X → ℤ} {g : X → ℚ_[2]}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => mk (f x) (g x) :=
  hf.prodMk hg

theorem continuous_two_zpow : Continuous fun n : ℤ => (2 : ℚ_[2]) ^ n :=
  continuous_of_discreteTopology

instance : IsTopologicalGroup AffineTwo where
  continuous_mul := by
    change Continuous fun p : AffineTwo × AffineTwo =>
      mk (power p.1 + power p.2) ((2 : ℚ_[2]) ^ power p.2 * offset p.1 + offset p.2)
    exact continuous_mk'
      ((continuous_power.comp continuous_fst).add (continuous_power.comp continuous_snd))
      (((continuous_two_zpow.comp (continuous_power.comp continuous_snd)).mul
        (continuous_offset.comp continuous_fst)).add (continuous_offset.comp continuous_snd))
  continuous_inv := by
    change Continuous fun x : AffineTwo =>
      mk (-power x) (-((2 : ℚ_[2]) ^ (-power x) * offset x))
    exact continuous_mk' continuous_power.neg
      ((continuous_two_zpow.comp continuous_power.neg).mul continuous_offset).neg

theorem isLocallyProfinite : Langlands.Topology.IsLocallyProfinite AffineTwo :=
  Langlands.Topology.isLocallyProfinite_of_mathlib

/-- The closed subgroup of linear maps `x ↦ 2 ^ n * x`, the points `(n, 0)`. -/
def linearSubgroup : Subgroup AffineTwo where
  carrier := {x | offset x = 0}
  mul_mem' {x y} hx hy := by
    change offset x = 0 at hx
    change offset y = 0 at hy
    change offset (x * y) = 0
    simp [hx, hy]
  one_mem' := offset_one
  inv_mem' {x} hx := by
    change offset x = 0 at hx
    change offset x⁻¹ = 0
    simp [hx]

theorem isClosed_linearSubgroup : IsClosed (linearSubgroup : Set AffineTwo) :=
  isClosed_eq continuous_offset continuous_const

/-- The homogeneous quotient `H\G`. -/
abbrev HomogeneousSpace := Langlands.Induction.LeftQuotient linearSubgroup

theorem offset_eq_of_rel {x y : AffineTwo}
    (h : QuotientGroup.rightRel linearSubgroup x y) : offset x = offset y := by
  have hm := QuotientGroup.rightRel_apply.mp h
  change offset (y * x⁻¹) = 0 at hm
  simp only [offset_mul, offset_inv, power_inv] at hm
  exact mul_left_cancel₀ (zpow_ne_zero (-power x) (two_ne_zero : (2 : ℚ_[2]) ≠ 0))
    (by linear_combination -hm)

/-- The second coordinate identifies `H\G` with `ℚ_[2]`. -/
def coordinate : HomogeneousSpace ≃ₜ ℚ_[2] where
  toFun := Quotient.lift offset (fun _ _ h => offset_eq_of_rel h)
  invFun b := Quotient.mk _ (mk 0 b)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h x =>
      apply Quotient.sound
      change QuotientGroup.rightRel linearSubgroup (mk 0 (offset x)) x
      rw [QuotientGroup.rightRel_apply]
      change offset (x * (mk 0 (offset x))⁻¹) = 0
      simp
  right_inv b := rfl
  continuous_toFun := continuous_offset.quotient_lift _
  continuous_invFun :=
    continuous_quotient_mk'.comp (continuous_mk' continuous_const continuous_id)

theorem coordinate_rightTranslate (g : AffineTwo) (q : HomogeneousSpace) :
    coordinate (Langlands.QuotientIntegration.rightTranslate linearSubgroup g q) =
      (2 : ℚ_[2]) ^ power g * coordinate q + offset g := by
  induction q using Quotient.inductionOn with
  | h x => rfl

end AffineTwo

open AffineTwo

/-- The indicator of the closed unit ball of `ℚ_[2]`, as a test function. -/
def ballTest : SchwartzBruhat ℚ_[2] :=
  Hecke.TestFunction.characteristic
    (IsUltrametricDist.isClopen_closedBall (0 : ℚ_[2]) one_ne_zero)
    (isCompact_closedBall (0 : ℚ_[2]) 1)

/-- The same indicator on `H\G`, through the coordinate. -/
def quotientTest : SchwartzBruhat HomogeneousSpace :=
  Hecke.TestFunction.pullback coordinate ballTest

/-- The right translation by `(1, 0)`, which is `x ↦ 2 * x` in the coordinate. -/
def doubling : HomogeneousSpace ≃ₜ HomogeneousSpace :=
  Langlands.QuotientIntegration.rightTranslate linearSubgroup (mk 1 0)

/-- The nonnegative difference of the translated and the original indicator. -/
def differenceTest : SchwartzBruhat HomogeneousSpace :=
  Hecke.TestFunction.pullback doubling quotientTest - quotientTest

theorem ballTest_apply (y : ℚ_[2]) :
    ballTest y = if ‖y‖ ≤ 1 then 1 else 0 := by
  change (Metric.closedBall (0 : ℚ_[2]) 1).indicator (fun _ => (1 : ℂ)) y = _
  by_cases h : ‖y‖ ≤ 1
  · rw [Set.indicator_of_mem (by simpa using h)]
    simp only [h, ↓reduceIte]
  · rw [Set.indicator_of_notMem (by simpa using h)]
    simp only [h, ↓reduceIte]

theorem differenceTest_apply (q : HomogeneousSpace) :
    differenceTest q = ballTest (2 * coordinate q) - ballTest (coordinate q) := by
  change ballTest (coordinate (doubling q)) - ballTest (coordinate q) = _
  rw [doubling, coordinate_rightTranslate]
  simp

theorem norm_two_lt_one : ‖(2 : ℚ_[2])‖ < 1 := by
  simpa using Padic.norm_p_lt_one (p := 2)

theorem differenceTest_nonnegative : Distribution.IsNonnegativeTest differenceTest := by
  intro q
  rw [differenceTest_apply, ballTest_apply, ballTest_apply]
  by_cases h₁ : ‖coordinate q‖ ≤ 1
  · have h₂ : ‖2 * coordinate q‖ ≤ 1 := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right norm_two_lt_one.le (norm_nonneg _)).trans
        (by simpa using h₁)
    simp only [h₁, h₂, ↓reduceIte, sub_self, Complex.zero_im, Complex.zero_re, le_refl,
      and_self]
  · by_cases h₂ : ‖2 * coordinate q‖ ≤ 1
    · simp only [h₁, h₂, ↓reduceIte, sub_zero, Complex.one_im, Complex.one_re, zero_le_one,
        and_self]
    · simp only [h₁, h₂, ↓reduceIte, sub_self, Complex.zero_im, Complex.zero_re, le_refl,
        and_self]

theorem differenceTest_ne_zero : differenceTest ≠ 0 := by
  intro h
  have hq :=
    congrArg (fun φ : SchwartzBruhat HomogeneousSpace => φ (coordinate.symm 2⁻¹)) h
  change differenceTest (coordinate.symm 2⁻¹) = 0 at hq
  rw [differenceTest_apply, Homeomorph.apply_symm_apply, ballTest_apply,
    ballTest_apply] at hq
  have hinv : ¬ ‖(2 : ℚ_[2])⁻¹‖ ≤ 1 := by
    rw [norm_inv, not_le]
    exact one_lt_inv₀ (norm_pos_iff.mpr two_ne_zero) |>.mpr norm_two_lt_one
  rw [mul_inv_cancel₀ two_ne_zero, norm_one] at hq
  simp only [hinv, le_refl, ↓reduceIte, sub_zero, one_ne_zero] at hq

end Nonexistence

open Nonexistence Nonexistence.AffineTwo in
/-- Renard II.3.9, first paragraph: the actual homogeneous quotient of the
affine group of `ℚ_[2]` by its linear subgroup carries no strictly positive
right-translation-invariant functional on its test functions. -/
theorem nonexistence : NonexistenceStatement := by
  refine ⟨AffineTwo, inferInstance, inferInstance, inferInstance,
    AffineTwo.isLocallyProfinite, linearSubgroup, isClosed_linearSubgroup, ?_⟩
  rintro ⟨T, hpos, hinv⟩
  have htrans : T (Hecke.TestFunction.pullback doubling quotientTest) = T quotientTest :=
    congrArg (fun S : Distribution HomogeneousSpace => S quotientTest) (hinv (mk 1 0))
  have hzero : T differenceTest = 0 := by
    rw [differenceTest, map_sub, htrans, sub_self]
  have hposD := (hpos differenceTest differenceTest_ne_zero differenceTest_nonnegative).2
  rw [hzero] at hposD
  exact lt_irrefl _ hposD

end Langlands.HarmonicAnalysis.HomogeneousFunctions.Renard
