import Langlands.Group.GL.BruhatNormalMatrixDirections
import Langlands.Group.GL.RealBruhatTrailingChart

/-! # Tangent and normal coordinates near a real Bruhat cell -/

noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GeneralLinear.RealBruhatProductChart

open RealBruhatTrailingChart

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "GLₙ" => Langlands.GeneralLinear n ℝ

/-- The coordinate positions transverse to the cell. -/
abbrev IsNormalEntry (w : Equiv.Perm (Fin n)) (ij : Fin n × Fin n) : Prop :=
  Langlands.GeneralLinear.bruhatNormalEntry w ij.1 ij.2

instance decidableBruhatNormalEntry (w : Equiv.Perm (Fin n)) (i j : Fin n) :
    Decidable (Langlands.GeneralLinear.bruhatNormalEntry w i j) :=
  inferInstanceAs (Decidable (j < i ∧ w.symm j < w.symm i))

/-- Coordinate arrays along the Bruhat cell. -/
abbrev Tangent (w : Equiv.Perm (Fin n)) := {ij : Fin n × Fin n // ¬ IsNormalEntry w ij} → ℝ

/-- Coordinate arrays normal to the Bruhat cell. -/
abbrev Normal (w : Equiv.Perm (Fin n)) := {ij : Fin n × Fin n // IsNormalEntry w ij} → ℝ

/-- Assemble the disjoint coordinate arrays into a matrix. -/
def combine (w : Equiv.Perm (Fin n)) : (Tangent w × Normal w) ≃L[ℝ] Mat :=
  ({ toFun := fun z i j => if h : IsNormalEntry w (i, j) then z.2 ⟨(i, j), h⟩ else z.1 ⟨(i, j), h⟩
     invFun := fun x => (fun ij => x ij.val.1 ij.val.2, fun ij => x ij.val.1 ij.val.2)
     left_inv := by
       intro z
       apply Prod.ext
       · funext ij
         rcases ij with ⟨⟨i, j⟩, h⟩
         exact dite_eq_right h
       · funext ij
         rcases ij with ⟨⟨i, j⟩, h⟩
         exact dite_eq_left h
     right_inv := by
       intro x
       ext i j
       by_cases h : IsNormalEntry w (i, j) <;> simp [h]
     map_add' := by
       intro x y
       ext i j
       by_cases h : IsNormalEntry w (i, j)
       · simp only [Matrix.add_apply, dite_eq_left h, Prod.snd_add, Pi.add_apply]
       · simp only [Matrix.add_apply, dite_eq_right h, Prod.fst_add, Pi.add_apply]
     map_smul' := by
       intro c x
       ext i j
       by_cases h : IsNormalEntry w (i, j) <;> simp [h] } :
    (Tangent w × Normal w) ≃ₗ[ℝ] Mat).toContinuousLinearEquiv

@[simp]
theorem combine_symm_normal (w : Equiv.Perm (Fin n)) (x : Mat)
    (ij : {ij : Fin n × Fin n // IsNormalEntry w ij}) :
    ((combine w).symm x).2 ij = x ij.val.1 ij.val.2 := rfl

/-- The diagonal is a tangent coordinate for every permutation. -/
def diagonalIndex (w : Equiv.Perm (Fin n)) (i : Fin n) :
    {ij : Fin n × Fin n // ¬ IsNormalEntry w ij} :=
  ⟨(i, i), fun h => lt_irrefl i h.1⟩

@[simp]
theorem combine_diagonal (w : Equiv.Perm (Fin n)) (z : Tangent w × Normal w) (i : Fin n) :
    combine w z i i = z.1 (diagonalIndex w i) := by
  change (if h : IsNormalEntry w (i, i) then z.2 ⟨(i, i), h⟩ else z.1 ⟨(i, i), h⟩) = _
  have h : ¬ IsNormalEntry w (i, i) := (diagonalIndex w i).property
  simp [h, diagonalIndex]

/-- The open condition on the tangent array is that all diagonal entries are nonzero. -/
def tangentDomain (w : Equiv.Perm (Fin n)) : Set (Tangent w) :=
  {x | ∀ i : Fin n, x (diagonalIndex w i) ≠ 0}

theorem isOpen_tangentDomain (w : Equiv.Perm (Fin n)) : IsOpen (tangentDomain w) := by
  have he : tangentDomain w = ⋂ i : Fin n, {x | x (diagonalIndex w i) ≠ 0} := by
    ext x
    simp [tangentDomain]
  rw [he]
  exact isOpen_iInter_of_finite fun i => isOpen_ne_fun (continuous_apply _) continuous_const

private theorem combine_mem_coordinateDomain (w : Equiv.Perm (Fin n)) (z : Tangent w × Normal w) :
    combine w z ∈ coordinateDomain n ↔ z.1 ∈ tangentDomain w := by
  simp only [coordinateDomain, tangentDomain, mem_ofPred_eq, combine_diagonal]

private def shift (w : Equiv.Perm (Fin n)) (y : Mat) : Mat := y * (permutation n ℝ w).val
private def unshift (w : Equiv.Perm (Fin n)) (y : Mat) : Mat := y * (permutation n ℝ w)⁻¹.val

private theorem unshift_shift (w : Equiv.Perm (Fin n)) (y : Mat) : unshift w (shift w y) = y := by
  rw [unshift, shift, Matrix.mul_assoc, show (permutation n ℝ w).val * (permutation n ℝ w)⁻¹.val = 1
    from (permutation n ℝ w).val_inv, mul_one]

private theorem shift_unshift (w : Equiv.Perm (Fin n)) (y : Mat) : shift w (unshift w y) = y := by
  rw [unshift, shift, Matrix.mul_assoc, show (permutation n ℝ w)⁻¹.val * (permutation n ℝ w).val = 1
    from (permutation n ℝ w).inv_val, mul_one]

private theorem contDiff_shift (w : Equiv.Perm (Fin n)) : ContDiff ℝ ∞ (shift w) :=
  contDiff_id.mul contDiff_const

private theorem contDiff_unshift (w : Equiv.Perm (Fin n)) : ContDiff ℝ ∞ (unshift w) :=
  contDiff_id.mul contDiff_const

/-- Shifted triangular coordinates on a product of the tangent domain and the
whole normal space. The zero normal slice is the actual Bruhat cell. -/
def productChart (w : Equiv.Perm (Fin n)) : OpenPartialHomeomorph (Tangent w × Normal w) Mat where
  toFun z := shift w (trailingChart n (combine w z))
  invFun y := (combine w).symm ((trailingChart n).symm (unshift w y))
  source := tangentDomain w ×ˢ univ
  target := unshift w ⁻¹' trailingDomain n
  map_source' z hz := by
    change unshift w (shift w (trailingChart n (combine w z))) ∈ trailingDomain n
    rw [unshift_shift]
    exact (trailingChart n).map_source ((combine_mem_coordinateDomain w z).2 hz.1)
  map_target' y hy := by
    refine ⟨(combine_mem_coordinateDomain w _).1 ?_, mem_univ _⟩
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact (trailingChart n).map_target hy
  left_inv' z hz := by
    rw [unshift_shift, (trailingChart n).left_inv ((combine_mem_coordinateDomain w z).2 hz.1),
      ContinuousLinearEquiv.symm_apply_apply]
  right_inv' y hy := by
    rw [ContinuousLinearEquiv.apply_symm_apply, (trailingChart n).right_inv hy, shift_unshift]
  open_source := (isOpen_tangentDomain w).prod isOpen_univ
  open_target := (isOpen_trailingDomain n).preimage (contDiff_unshift w).continuous
  continuousOn_toFun := (contDiff_shift w).continuous.comp_continuousOn
    ((trailingChart n).continuousOn.comp (combine w).continuous.continuousOn fun z hz =>
      (combine_mem_coordinateDomain w z).2 hz.1)
  continuousOn_invFun := (combine w).symm.continuous.comp_continuousOn
    ((trailingChart n).symm.continuousOn.comp (contDiff_unshift w).continuous.continuousOn fun _ h => h)

theorem contDiffOn_productChart (w : Equiv.Perm (Fin n)) :
    ContDiffOn ℝ ∞ (productChart w) (productChart w).source :=
  (contDiff_shift w).comp_contDiffOn ((contDiffOn_trailingChart n).comp
    (combine w).toContinuousLinearMap.contDiff.contDiffOn fun z hz =>
      (combine_mem_coordinateDomain w z).2 hz.1)

theorem contDiffOn_productChart_symm (w : Equiv.Perm (Fin n)) :
    ContDiffOn ℝ ∞ (productChart w).symm (productChart w).target :=
  (combine w).symm.toContinuousLinearMap.contDiff.comp_contDiffOn ((contDiffOn_trailingChart_symm n).comp
    (contDiff_unshift w).contDiffOn fun _ h => h)

theorem mem_productChart_target_of_mem_cell (w : Equiv.Perm (Fin n)) {g : GLₙ}
    (hg : g ∈ upperBruhatCell n ℝ w) : g.val ∈ (productChart w).target :=
  mem_trailingDomain_of_mem_cell w hg

theorem isUnit_of_mem_productChart_target (w : Equiv.Perm (Fin n)) {y : Mat}
    (hy : y ∈ (productChart w).target) : IsUnit y := by
  change unshift w y ∈ trailingDomain n at hy
  have h : IsUnit (shift w (unshift w y)) := hy.1.mul (permutation n ℝ w).isUnit
  rwa [shift_unshift] at h

/-- In the smooth product chart the cell is precisely the zero normal section. -/
theorem mem_cell_iff_normal_eq_zero (w : Equiv.Perm (Fin n)) {g : GLₙ}
    (hg : g.val ∈ (productChart w).target) :
    g ∈ upperBruhatCell n ℝ w ↔ ((productChart w).symm g.val).2 = 0 := by
  rw [mem_cell_iff_inverseValue_lower_zero w g hg]
  constructor
  · intro hz
    funext ij
    change ((combine w).symm ((trailingChart n).symm (unshift w g.val))).2 ij = 0
    rw [combine_symm_normal]
    exact hz _ _ ij.property.1 ij.property.2
  · intro hz i j hij hw
    exact congrFun hz (⟨(i, j), ⟨hij, hw⟩⟩ : {ij : Fin n × Fin n // IsNormalEntry w ij})

/-- Each real Bruhat cell has smooth product coordinates on an open matrix
neighborhood, with the cell exactly the zero set of the normal coordinate. -/
def RealBruhatProductChartStatement : Prop :=
  ∀ (n : ℕ) (w : Equiv.Perm (Fin n)),
    let e := productChart w
    e.source = tangentDomain w ×ˢ univ ∧
    (∀ y ∈ e.target, IsUnit y) ∧
    ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
    ∀ g : Langlands.GeneralLinear n ℝ,
      (g ∈ upperBruhatCell n ℝ w → g.val ∈ e.target) ∧
      (g.val ∈ e.target → (g ∈ upperBruhatCell n ℝ w ↔ (e.symm g.val).2 = 0))

theorem realBruhatProductChart : RealBruhatProductChartStatement :=
  fun _ w => ⟨rfl, fun _ => isUnit_of_mem_productChart_target w, contDiffOn_productChart w,
    contDiffOn_productChart_symm w, fun _ =>
      ⟨mem_productChart_target_of_mem_cell w, mem_cell_iff_normal_eq_zero w⟩⟩

end Langlands.GeneralLinear.RealBruhatProductChart
