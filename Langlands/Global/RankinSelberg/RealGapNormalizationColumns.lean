import Langlands.Global.RankinSelberg.RealGapNormalizationShear
import Langlands.Group.GL.LowerBlockQuotientCoordinates

/-! # Split real test arguments under leading determinant normalization -/

noncomputable section

open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapNormalizationColumns

open Langlands.GeneralLinear (inverseTranspose inverseTranspose_coe rankInclusion rankInclusion_val_submatrix
  blockSum_apply_left blockSum_apply_left_right blockSum_apply_right_left blockSum_apply_right)
open Langlands.RankinSelberg (lastRow_mul_eq_vecMul)
open RealGapAlternateWeighted (leadingSide)
open RealGapColumnFourier (transposeColumn triangularFourier)
open RealGapLeadingSchwartz (leadingStack)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℝ

/-- Inverse transpose on either side respects multiplication. -/
theorem leadingSide_mul {n : ℕ} (dual : Bool) (g z : G n) : leadingSide dual (g * z) = leadingSide dual g * leadingSide dual z := by
  cases dual
  · rfl
  · exact map_mul (inverseTranspose n ℝ) g z

/-- Inverse transpose on either side is an involution. -/
theorem leadingSide_involutive {n : ℕ} (dual : Bool) (g : G n) : leadingSide dual (leadingSide dual g) = g := by
  cases dual
  · rfl
  · exact Langlands.GeneralLinear.inverseTranspose_involutive n ℝ g

private theorem inverseTranspose_rankInclusion {k m : ℕ} (g : G k) :
    inverseTranspose (k + m) ℝ (rankInclusion m g) = rankInclusion m (inverseTranspose k ℝ g) := by
  apply Units.ext
  let e : Fin k ⊕ Fin m ≃ Fin (k + m) := finSumFinEquiv
  apply (Matrix.reindex e.symm e.symm).injective
  change ((inverseTranspose (k + m) ℝ (rankInclusion m g)).val).submatrix e e =
    (rankInclusion m (inverseTranspose k ℝ g)).val.submatrix e e
  rw [inverseTranspose_coe, ← map_inv, ← Matrix.transpose_submatrix,
    rankInclusion_val_submatrix, rankInclusion_val_submatrix, inverseTranspose_coe]
  simp only [Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_one]

private theorem rankInclusion_mulVec_tail {k m : ℕ} (g : G k) (v : Fin (k + m) → ℝ)
    (hv : ∀ i : Fin k, v (i.castAdd m) = 0) : (rankInclusion m g).val.mulVec v = v := by
  let e : Fin k ⊕ Fin m ≃ Fin (k + m) := finSumFinEquiv
  suffices h : ((rankInclusion m g).val.mulVec v) ∘ e = v ∘ e by
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    exact congrFun h j
  have he : (rankInclusion m g).val.submatrix e e = Matrix.fromBlocks g.val 0 0 (1 : Mat m m) :=
    rankInclusion_val_submatrix (d := m) g
  have hEq : ((rankInclusion m g).val.mulVec v) ∘ e =
      ((rankInclusion m g).val.submatrix e e).mulVec (v ∘ e) := by
    funext i
    simp only [Function.comp_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
    exact (Fintype.sum_equiv e (fun j => (rankInclusion m g).val (e i) (e j) * v (e j))
      (fun j => (rankInclusion m g).val (e i) j * v j) (fun _ => rfl)).symm
  rw [hEq, he, Matrix.fromBlocks_mulVec]
  have hZero : (v ∘ e) ∘ Sum.inl = (0 : Fin k → ℝ) := funext fun i => hv i
  rw [hZero]
  simp only [Matrix.mulVec_zero, Matrix.zero_mulVec, add_zero, zero_add, Matrix.one_mulVec]
  funext i
  cases i with
  | inl j => exact (hv j).symm
  | inr j => rfl

private theorem rankInclusion_tailColumn {k m : ℕ} (g : G k) (B : G (k + m)) (j : Fin m) :
    (fun i => (B * rankInclusion m g).val i (j.natAdd k)) = fun i => B.val i (j.natAdd k) := by
  let v (i : Fin (k + m)) := (1 : Mat (k + m) (k + m)) i (j.natAdd k)
  have hv (i : Fin k) : v (i.castAdd m) = 0 := by
    apply Matrix.one_apply_ne
    intro h
    have h' := congrArg Fin.val h
    change i.val = k + j.val at h'
    omega
  have hc : (fun i => (rankInclusion m g).val i (j.natAdd k)) = v := by
    have h := rankInclusion_mulVec_tail g v hv
    change (fun i => ((rankInclusion m g).val * (1 : Mat (k + m) (k + m))) i (j.natAdd k)) = _ at h
    rwa [Matrix.mul_one] at h
  change B.val.mulVec (fun i => (rankInclusion m g).val i (j.natAdd k)) = _
  rw [hc]
  change (fun i => (B.val * (1 : Mat (k + m) (k + m))) i (j.natAdd k)) = _
  rw [Matrix.mul_one]

private theorem rankInclusion_lastRow {k q : ℕ} (g : G k) :
    Langlands.RankinSelberg.lastRow (rankInclusion (q + 1) g) =
      Langlands.RankinSelberg.lastRow (1 : G (k + q + 1)) := by
  funext j
  have hl : (Fin.last q).natAdd k = Fin.last (k + q) := Fin.ext rfl
  change (rankInclusion (q + 1) g).val (Fin.last (k + q)) j = (1 : Mat (k + q + 1) (k + q + 1)) (Fin.last (k + q)) j
  rw [← hl]
  refine Fin.addCases (m := k) (n := q + 1) (fun j₀ => ?_) (fun j₁ => ?_) j
  · rw [show (rankInclusion (q + 1) g).val ((Fin.last q).natAdd k) (j₀.castAdd (q + 1)) = 0 from
      blockSum_apply_right_left g 1 (Fin.last q) j₀]
    rw [Matrix.one_apply_ne]
    intro he
    have he' := congrArg Fin.val he
    change k + q = j₀.val at he'
    omega
  · rw [show (rankInclusion (q + 1) g).val ((Fin.last q).natAdd k) (j₁.natAdd k) =
      (1 : Mat (q + 1) (q + 1)) (Fin.last q) j₁ from blockSum_apply_right g 1 (Fin.last q) j₁,
      Matrix.one_apply, Matrix.one_apply]
    simp only [Fin.natAdd_inj]

private theorem rankInclusion_mulVec_of_append {k m : ℕ} (g : G k) (x : Fin k → ℝ) (y : Fin m → ℝ) :
    (rankInclusion m g).val.mulVec (Fin.append x y) = Fin.append (g.val.mulVec x) y := by
  ext i
  refine Fin.addCases (m := k) (n := m) (fun i₀ => ?_) (fun i₁ => ?_) i
  · change (∑ j, (rankInclusion m g).val (i₀.castAdd m) j * Fin.append x y j) = _
    rw [Fin.sum_univ_add (a := k) (b := m)]
    simp [rankInclusion, Matrix.mulVec, dotProduct]
  · change (∑ j, (rankInclusion m g).val (i₁.natAdd k) j * Fin.append x y j) = _
    rw [Fin.sum_univ_add (a := k) (b := m)]
    simp [rankInclusion, Matrix.one_apply]

private theorem rankInclusion_mul_leadingStack {k m : ℕ} (g h : G k) (Y : Mat m k) :
    (rankInclusion m g).val * leadingStack h.val Y = leadingStack (g * h).val Y := by
  ext i j
  exact congrFun (rankInclusion_mulVec_of_append g (fun a => h.val a j) (fun a => Y a j)) i

/-- Right multiplication by the leading block rescales exactly the square part of the leading test. -/
theorem leadingSide_mul_stack {k m : ℕ} (dual : Bool) (B : G (k + m)) (g h : G k) (Y : Mat m k) :
    (leadingSide dual (B * rankInclusion m g)).val * leadingStack (leadingSide dual h).val Y =
      (leadingSide dual B).val * leadingStack (leadingSide dual (g * h)).val Y := by
  have hι : leadingSide dual (rankInclusion m g) = rankInclusion m (leadingSide dual g) := by
    cases dual
    · rfl
    · exact inverseTranspose_rankInclusion g
  rw [leadingSide_mul, hι, Units.val_mul, Matrix.mul_assoc, rankInclusion_mul_leadingStack, ← leadingSide_mul]

set_option maxHeartbeats 700000 in
/-- The earlier triangular Fourier columns are insensitive to any invertible leading block. -/
theorem triangularFourier_right_rankInclusion {k q : ℕ} (a : ℝˣ)
    (B : G (k + q + 1)) (g : G k) (Ξ : Fin q → 𝓢((Fin (k + q + 1) → ℝ), ℂ)) (Z : N (q + 1)) :
    triangularFourier k q a (B * rankInclusion (q + 1) g) Ξ Z = triangularFourier k q a B Ξ Z := by
  unfold triangularFourier
  apply congrArg (fun x : ℂ => x * (Whittaker.standardCharacter
    (Langlands.LocalFactor.Archimedean.realScaledCharacter a) q Z : ℂ))
  refine Finset.prod_congr rfl fun j _ => ?_
  let v := transposeColumn k q Z⁻¹ j
  have hv (i : Fin k) : v (i.castAdd (q + 1)) = 0 := by
    unfold v transposeColumn
    exact ite_eq_left (show (i.castAdd (q + 1)).val < k from i.isLt)
  have h : (B * rankInclusion (q + 1) g)⁻¹.val.transpose.mulVec v = B⁻¹.val.transpose.mulVec v := by
    change (inverseTranspose (k + (q + 1)) ℝ (B * rankInclusion (q + 1) g)).val.mulVec v = _
    rw [map_mul, inverseTranspose_rankInclusion (m := q + 1), Units.val_mul, ← Matrix.mulVec_mulVec,
      rankInclusion_mulVec_tail _ _ hv, inverseTranspose_coe]
  exact congrArg (ArchimedeanLocal.realFourierTransform a (Ξ j)) h

/-- Right multiplication by a leading block fixes the first tail column and the inverse last row. -/
theorem tailEndpoints_right_rankInclusion {k q : ℕ} (B : G (k + q + 1)) (g : G k) :
    (fun i => (B * rankInclusion (q + 1) g).val i ((0 : Fin (q + 1)).natAdd k)) =
      (fun i => B.val i ((0 : Fin (q + 1)).natAdd k)) ∧
    Langlands.RankinSelberg.lastRow ((B * rankInclusion (q + 1) g)⁻¹) = Langlands.RankinSelberg.lastRow B⁻¹ := by
  refine ⟨rankInclusion_tailColumn (m := q + 1) g B 0, ?_⟩
  rw [mul_inv_rev, ← map_inv (rankInclusion (q + 1)) g, lastRow_mul_eq_vecMul,
    rankInclusion_lastRow, ← lastRow_mul_eq_vecMul, one_mul]

/-- The complete split test transforms by a leading coordinate change, fixing all the tail factors. -/
def RealGapNormalizationColumnsStatement : Prop :=
  ∀ (k q : ℕ) (dual : Bool) (a : ℝˣ) (B : G (k + q + 1)) (g h : G k) (Y : Mat (q + 1) k)
    (Ξ : Fin q → 𝓢((Fin (k + q + 1) → ℝ), ℂ)) (Z : N (q + 1)),
    (leadingSide dual (B * rankInclusion (q + 1) g)).val * leadingStack (leadingSide dual h).val Y =
      (leadingSide dual B).val * leadingStack (leadingSide dual (g * h)).val Y ∧
    triangularFourier k q a (B * rankInclusion (q + 1) g) Ξ Z = triangularFourier k q a B Ξ Z ∧
    (fun i => (B * rankInclusion (q + 1) g).val i ((0 : Fin (q + 1)).natAdd k)) =
      (fun i => B.val i ((0 : Fin (q + 1)).natAdd k)) ∧
    Langlands.RankinSelberg.lastRow ((B * rankInclusion (q + 1) g)⁻¹) = Langlands.RankinSelberg.lastRow B⁻¹

theorem realGapNormalizationColumns : RealGapNormalizationColumnsStatement := by
  intro k q dual a B g h Y Ξ Z
  exact ⟨leadingSide_mul_stack (m := q + 1) dual B g h Y, triangularFourier_right_rankInclusion a B g Ξ Z,
    tailEndpoints_right_rankInclusion B g⟩

end Langlands.Global.RankinSelbergGlobal.RealGapNormalizationColumns
