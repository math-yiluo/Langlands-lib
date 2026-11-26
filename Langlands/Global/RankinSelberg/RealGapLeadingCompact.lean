import Langlands.Global.RankinSelberg.RealGapDualChart
import Langlands.Global.RankinSelberg.RealGapLeadingFourier
import Langlands.Global.RankinSelberg.RealAdjacentGaussianSplit
import Langlands.Global.RankinSelberg.RealUnequalPairConvergence

/-! # The compact span of the leading Gaussian restriction -/

noncomputable section

open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapLeadingCompact

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (rankInclusion blockSum)
open RealGapTriangularChart (Outer retainedMatrix)
open RealGapUnitDeterminant (leadingScalar unitRetained normalizingScalar)
open RealGapUpperTail (packedTail packedTail_top_left packedTail_bottom_left firstRectangle)
open RealGapDualChart (retainedTail)
open RealGapLeadingFourier (stackRows stackRows_left stackRows_right leadingRestriction leadingRestriction_apply)
open RealGodementGaussianPolynomial (Coordinates gaussianPolynomial)
open RealJacquet (finiteDimensional_gaussianPolynomial_left)

variable (k q : ℕ)
local notation "Size" => k + q + 1
local notation "TailSize" => q + 1
local notation "Small" => Matrix (Fin k) (Fin k) ℝ
local notation "Leading" => Matrix (Fin Size) (Fin k) ℝ
local notation "H" => Langlands.GeneralLinear k ℝ
local notation "G" => Langlands.GeneralLinear Size ℝ
local notation "N" => Langlands.GeneralLinear.upperUnipotent TailSize ℝ
local notation "K" => unitaryCompact ℝ Size
local notation "Ksmall" => unitaryCompact ℝ k

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
private theorem blockSum_stack (g : H) (h : Langlands.GeneralLinear TailSize ℝ) (X : Small) :
    (blockSum (g, h)).val * stackRows k TailSize k X 0 = stackRows k TailSize k (g.val * X) 0 := by
  ext i j
  refine Fin.addCases (m := k) (n := TailSize) (fun i₀ => ?_) (fun i₁ => ?_) i
  · rw [Matrix.mul_apply, Fin.sum_univ_add (a := k) (b := TailSize), stackRows_left, Matrix.mul_apply]
    simp only [Langlands.GeneralLinear.blockSum_apply_left, stackRows_left, stackRows_right,
      Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  · rw [Matrix.mul_apply, Fin.sum_univ_add (a := k) (b := TailSize), stackRows_right]
    simp only [Langlands.GeneralLinear.blockSum_apply_right_left, stackRows_left, stackRows_right,
      Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]

/-- An upper packed tail acts trivially on a stack with zero trailing rows. -/
theorem packedTail_stack (Y : Matrix (Fin k) (Fin TailSize) ℝ) (Z : N) (X : Small) :
    (packedTail k q Y Z).val.val * stackRows k TailSize k X 0 = stackRows k TailSize k X 0 := by
  let P : Matrix (Fin (k + TailSize)) (Fin (k + TailSize)) ℝ := (packedTail k q Y Z).val.val
  have h11 (i j : Fin k) : P (Fin.castAdd TailSize i) (Fin.castAdd TailSize j) = (1 : Small) i j :=
    packedTail_top_left k q Y Z i j
  have h21 (i : Fin TailSize) (j : Fin k) : P (Fin.natAdd k i) (Fin.castAdd TailSize j) = 0 :=
    packedTail_bottom_left k q Y Z i j
  change P * stackRows k TailSize k X 0 = _
  ext i j
  refine Fin.addCases (m := k) (n := TailSize) (fun i₀ => ?_) (fun i₁ => ?_) i
  · rw [Matrix.mul_apply, Fin.sum_univ_add (a := k) (b := TailSize), stackRows_left]
    simp only [h11, stackRows_left, stackRows_right, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  · rw [Matrix.mul_apply, Fin.sum_univ_add (a := k) (b := TailSize), stackRows_right]
    simp only [h21, stackRows_left, stackRows_right, Matrix.zero_apply, mul_zero,
      zero_mul, Finset.sum_const_zero, add_zero]

/-- The leading restriction on the retained chart depends only on the compact matrix and leading scalar. -/
theorem retainedTail_stack (p : Outer k q) (Z : N) (X : Small) :
    (retainedTail k q p Z).val * stackRows k TailSize k X 0 =
      p.1.2.val.val * stackRows k TailSize k ((leadingScalar k q p.1.1.2).val * X) 0 := by
  unfold retainedTail unitRetained retainedMatrix
  simp only [Units.val_mul, Matrix.mul_assoc, packedTail_stack]
  have hInc : (rankInclusion TailSize (leadingScalar k q p.1.1.2)).val * stackRows k TailSize k X 0 =
      stackRows k TailSize k ((leadingScalar k q p.1.1.2).val * X) 0 := blockSum_stack k q _ 1 X
  rw [hInc, packedTail_stack, blockSum_stack, Units.val_one, Matrix.one_mul]

private def embedded (u : Ksmall) : K :=
  ⟨rankInclusion TailSize u.val,
    RealUnequalPairConvergence.blockSum_mem_unitary u.2 (Subgroup.one_mem _)⟩

private theorem retainedTail_stack_covariant (p : Outer k q) (Z : N) (u : Ksmall) (X : Small) :
    (retainedTail k q p Z).val * stackRows k TailSize k (u⁻¹.val.val * X) 0 =
      ((p.1.2 * embedded k q u * p.1.2⁻¹)⁻¹).val.val *
        ((retainedTail k q p Z).val * stackRows k TailSize k X 0) := by
  let S := leadingScalar k q p.1.1.2
  let Kc := p.1.2
  have hQ : ((Kc * embedded k q u * Kc⁻¹)⁻¹).val * Kc.val = Kc.val * rankInclusion TailSize u⁻¹.val := by
    change (Kc.val * rankInclusion TailSize u.val * Kc.val⁻¹)⁻¹ * Kc.val = _
    rw [Subgroup.coe_inv, map_inv]
    group
  have hS : S.val * (u⁻¹).val.val = (u⁻¹).val.val * S.val := by
    exact congrArg Units.val (Matrix.GeneralLinearGroup.scalar_commute (normalizingScalar k q p.1.1.2) u⁻¹.val)
  simp only [retainedTail_stack]
  change Kc.val.val * stackRows k TailSize k (S.val * (u⁻¹.val.val * X)) 0 =
    ((Kc * embedded k q u * Kc⁻¹)⁻¹).val.val *
      (Kc.val.val * stackRows k TailSize k (S.val * X) 0)
  have hM : ((Kc * embedded k q u * Kc⁻¹)⁻¹).val.val * Kc.val.val =
      Kc.val.val * (rankInclusion TailSize u⁻¹.val).val := congrArg Units.val hQ
  have hEmb : (rankInclusion TailSize u⁻¹.val).val * stackRows k TailSize k (S.val * X) 0 =
      stackRows k TailSize k (u⁻¹.val.val * (S.val * X)) 0 := blockSum_stack k q _ 1 _
  rw [← Matrix.mul_assoc ((Kc * embedded k q u * Kc⁻¹)⁻¹).val.val, hM, Matrix.mul_assoc,
    hEmb, ← Matrix.mul_assoc S.val, hS, Matrix.mul_assoc]

/-- A leading polynomial Gaussian remains finite under left translations by the small unitary group. -/
def RealGapLeadingCompactStatement : Prop :=
  ∀ (p : Outer k q) (Z : N) (P : MvPolynomial (Coordinates Size k) ℂ),
    let Ξ := leadingRestriction k TailSize k (retainedTail k q p Z) (gaussianPolynomial P)
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun u : Ksmall => fun X : Small => Ξ (u⁻¹.val.val * X)))

theorem realGapLeadingCompact : RealGapLeadingCompactStatement k q := by
  intro p Z P Ξ
  let Φ := gaussianPolynomial P
  let C := retainedTail k q p Z
  let L : (Leading → ℂ) →ₗ[ℂ] (Small → ℂ) :=
    { toFun := fun f X => f (C.val * stackRows k TailSize k X 0)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let F := Submodule.span ℂ (Set.range fun u : K => fun Y : Leading => Φ (u⁻¹.val.val * Y))
  let : FiniteDimensional ℂ F :=
    finiteDimensional_gaussianPolynomial_left (unitaryCompact ℝ Size).subtype (fun u => u.2) P
  let E := Submodule.span ℂ (Set.range fun u : Ksmall => fun X : Small => Ξ (u⁻¹.val.val * X))
  have hE : E ≤ F.map L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨u, rfl⟩
    let U := p.1.2 * embedded k q u * p.1.2⁻¹
    have hU : (fun Y : Leading => Φ (U⁻¹.val.val * Y)) ∈ F := Submodule.subset_span ⟨U, rfl⟩
    refine ⟨_, hU, ?_⟩
    funext X
    change Φ (U⁻¹.val.val * (C.val * stackRows k TailSize k X 0)) =
      Φ (C.val * stackRows k TailSize k (u⁻¹.val.val * X) 0)
    exact congrArg Φ (retainedTail_stack_covariant k q p Z u X).symm
  exact Submodule.finiteDimensional_of_le hE

end Langlands.Global.RankinSelbergGlobal.RealGapLeadingCompact
