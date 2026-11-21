import Langlands.Global.RankinSelberg.ComplexBruhatChartDerivative

/-! # Linearization of stabilizing directions in the complex Gauss chart -/

noncomputable section

open Filter Set
open scoped Classical ContDiff Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexBruhatLinearization

open Langlands.GeneralLinear (upperTriangularSubgroup)
open Langlands.Archimedean (borelChar isOpen_setOf_isUnit_matrix)
open ComplexOppositeCompactChart (Coordinates)
open ComplexBruhatGaussChart (chartCoordinates chartMatrixDomain chartDomain chartSection chartUpper
  cellCoordinates chart_recover chart_factorization chart_left_mul chartUpper_mem contDiffOn_chartCoordinates
  isOpen_chartMatrixDomain)
open ComplexBruhatTestExtension (chartUpperMatrix chartUpperMatrix_val chartUnitMatrixDomain
  isOpen_chartUnitMatrixDomain contDiffOn_chartUpperMatrix inducingMultiplier inducingMultiplier_one
  contDiffOn_chartMultiplier)
open ComplexBruhatChartDerivative (contDiff_chartSection_val chartVector chartScalar)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)

local notation "Mat" => fun n => Matrix (Fin n) (Fin n) ℂ
local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "B" => fun n => Langlands.GeneralLinear.upperTriangularSubgroup n ℂ

variable {n : ℕ}

private theorem chartSection_data (w : Equiv.Perm (Fin n)) (z : Coordinates n) :
    chartSection w z ∈ chartDomain w ∧ chartCoordinates w (chartSection w z).val = z ∧
      chartUpper w (chartSection w z) = 1 := by
  simpa only [Subgroup.coe_one, one_mul] using chart_recover w (1 : B n) z

/-- An affine upper triangular matrix line is a Borel element near the identity. -/
theorem eventually_upper_line (A : Mat n) (hA : A.IsUpperTriangular) :
    ∀ᶠ t : ℝ in 𝓝 0, ∃ b : B n, b.val.val = 1 + t • A := by
  have hAt : ContinuousAt (fun t : ℝ => (1 : Mat n) + t • A) 0 :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have h1 : IsUnit ((1 : Mat n) + (0 : ℝ) • A) := by simp
  filter_upwards [hAt (isOpen_setOf_isUnit_matrix.mem_nhds h1)] with t ht
  change IsUnit ((1 : Mat n) + t • A) at ht
  refine ⟨⟨ht.unit, ?_⟩, ht.unit_spec⟩
  change ht.unit.val.IsUpperTriangular
  rw [ht.unit_spec]
  intro i j hij
  change j < i at hij
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hij.ne', hA hij, smul_zero, add_zero]

private theorem hasDerivAt_left_line (A : Mat n) (g : G n) :
    HasDerivAt (fun t : ℝ => (1 + t • A) * g.val) (A * g.val) 0 := by
  simpa only [add_mul, one_mul, smul_mul_assoc, id_eq, one_smul] using
    ((hasDerivAt_id (0 : ℝ)).smul_const (A * g.val)).const_add g.val

/-- The coordinate differential kills the vertical directions of the left Borel action. -/
theorem coordDifferential_vertical (w : Equiv.Perm (Fin n)) (g : G n) (hg : g ∈ chartDomain w)
    (A : Mat n) (hA : A.IsUpperTriangular) :
    fderiv ℝ (chartCoordinates w) g.val (A * g.val) = 0 := by
  have he : (fun t : ℝ => chartCoordinates w ((1 + t • A) * g.val)) =ᶠ[𝓝 0]
      (fun _ => chartCoordinates w g.val) := by
    filter_upwards [eventually_upper_line A hA] with t ht
    obtain ⟨b, hb⟩ := ht
    rw [← hb]
    exact (chart_left_mul w b g hg).2.1
  have hd := ((contDiffOn_chartCoordinates w).contDiffAt
    ((isOpen_chartMatrixDomain w).mem_nhds hg)).differentiableAt (by simp)
  have hp := (hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_left_line A g) (by simp)).deriv
  change deriv (fun t : ℝ => chartCoordinates w ((1 + t • A) * g.val)) 0 = _ at hp
  rw [he.deriv_eq, deriv_const] at hp
  exact hp.symm

private theorem scalarDifferential_vertical (w : Equiv.Perm (Fin n)) (ds : List ComplexCharacterData)
    (z : Coordinates n) (A : Mat n) (hA : ∀ i j, j ≤ i → A i j = 0) :
    fderiv ℝ (fun Y => inducingMultiplier ds (chartUpperMatrix w Y)) (chartSection w z).val
      (A * (chartSection w z).val) = 0 := by
  let g := chartSection w z
  let m := fun Y => inducingMultiplier ds (chartUpperMatrix w Y)
  obtain ⟨hg, _, hb⟩ := chartSection_data w z
  have hU : g.val ∈ chartUnitMatrixDomain w := ⟨g.isUnit, hg⟩
  have he : (fun t : ℝ => m ((1 + t • A) * g.val)) =ᶠ[𝓝 0] (fun _ => (1 : ℂ)) := by
    filter_upwards [eventually_upper_line A (fun i j hij => hA i j hij.le)] with t ht
    obtain ⟨b, hb'⟩ := ht
    rw [← hb']
    change inducingMultiplier ds (chartUpperMatrix w (b.val * g).val) = 1
    rw [chartUpperMatrix_val, (chart_left_mul w b g hg).2.2, hb, mul_one, hb', ← inducingMultiplier_one (n := n) ds]
    unfold inducingMultiplier borelChar
    apply Finset.prod_congr rfl
    intro i _
    rw [Matrix.add_apply, Matrix.smul_apply, hA i i le_rfl, smul_zero, add_zero]
  have hd : DifferentiableAt ℝ m g.val := ((contDiffOn_chartMultiplier w ds).contDiffAt
    ((isOpen_chartUnitMatrixDomain w).mem_nhds hU)).differentiableAt (by simp)
  have hp := (hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_left_line A g) (by simp)).deriv
  change deriv (fun t : ℝ => m ((1 + t • A) * g.val)) 0 = _ at hp
  rw [he.deriv_eq, deriv_const] at hp
  exact hp.symm

private def linearizedAction (A X : Mat n) : Mat n →L[ℝ] Mat n :=
  (ContinuousLinearMap.mul ℝ (Mat n)).flip X - ContinuousLinearMap.mul ℝ (Mat n) A

private theorem linearizedAction_apply (A X Y : Mat n) : linearizedAction A X Y = Y * X - A * Y := rfl

private theorem linearizedAction_cube (A X : Mat n) (hA : A * A = 0) (hX : X * X = 0) (Y : Mat n) :
    linearizedAction A X (linearizedAction A X (linearizedAction A X Y)) = 0 := by
  have hXX (Y : Mat n) : Y * X * X = 0 := by rw [mul_assoc, hX, mul_zero]
  have hAA (Y : Mat n) : A * (A * Y) = 0 := by rw [← mul_assoc, hA, zero_mul]
  have h₂ (Y : Mat n) : linearizedAction A X (linearizedAction A X Y) = -(A * Y) * X - A * (Y * X) := by
    simp only [linearizedAction_apply, sub_mul, mul_sub, hXX, hAA, zero_sub, sub_zero, neg_mul]
  rw [h₂ (linearizedAction A X Y), linearizedAction_apply]
  simp only [mul_sub, sub_mul, hXX, sub_zero, zero_sub, mul_assoc A Y X, hAA]
  rw [neg_mul, mul_assoc A (Y * X) X, hXX, mul_zero, neg_zero, mul_neg, hAA, neg_zero, sub_zero]

private theorem upperDifferential_upper (w : Equiv.Perm (Fin n)) (g : G n) (hg : g ∈ chartDomain w)
    (Y : Mat n) : (fderiv ℝ (chartUpperMatrix w) g.val Y).IsUpperTriangular := by
  have hU : g.val ∈ chartUnitMatrixDomain w := ⟨g.isUnit, hg⟩
  have hd := ((contDiffOn_chartUpperMatrix w).mono (show chartUnitMatrixDomain w ⊆ chartMatrixDomain w from
    inter_subset_right)).contDiffAt ((isOpen_chartUnitMatrixDomain w).mem_nhds hU)
  intro i j hij
  let e := (Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap
  have he : (fun M => e (chartUpperMatrix w M)) =ᶠ[𝓝 g.val] (fun _ => (0 : ℂ)) := by
    filter_upwards [(isOpen_chartUnitMatrixDomain w).mem_nhds hU] with M hM
    let g' : G n := hM.1.unit
    have hg' : g' ∈ chartDomain w := show g'.val ∈ chartMatrixDomain w from hM.1.unit_spec.symm ▸ hM.2
    rw [← hM.1.unit_spec, chartUpperMatrix_val]
    exact chartUpper_mem w g' hg' hij
  have hh := (e.hasFDerivAt.comp g.val (hd.differentiableAt (by simp)).hasFDerivAt).fderiv
  change fderiv ℝ (fun M => e (chartUpperMatrix w M)) g.val = _ at hh
  rw [he.fderiv_eq] at hh
  have h := DFunLike.congr_fun hh Y
  change (fderiv ℝ (fun _ : Mat n => (0 : ℂ)) g.val) Y = _ at h
  simpa [e] using h.symm

private theorem gaussDifferential_factorization (w : Equiv.Perm (Fin n)) (z : Coordinates n) (Y : Mat n) :
    fderiv ℝ (chartUpperMatrix w) (chartSection w z).val Y * (chartSection w z).val +
      fderiv ℝ (fun q => (chartSection w q).val) z
        (fderiv ℝ (chartCoordinates w) (chartSection w z).val Y) = Y := by
  let S := fun q => (chartSection w q).val
  let g := chartSection w z
  let C := chartCoordinates w
  let U := chartUpperMatrix w
  obtain ⟨hg, hc, hb⟩ := chartSection_data w z
  have hU : g.val ∈ chartUnitMatrixDomain w := ⟨g.isUnit, hg⟩
  have hI : (fun M => U M * S (C M)) =ᶠ[𝓝 g.val] id := by
    filter_upwards [(isOpen_chartUnitMatrixDomain w).mem_nhds hU] with M hM
    let g' : G n := hM.1.unit
    rw [← hM.1.unit_spec]
    change chartUpperMatrix w g'.val * (chartSection w (chartCoordinates w g'.val)).val = g'.val
    rw [chartUpperMatrix_val, ← Units.val_mul, chart_factorization]
  have hgM : g.val ∈ chartMatrixDomain w := hg
  have hV := (isOpen_chartMatrixDomain w).mem_nhds hgM
  have hDu := ((contDiffOn_chartUpperMatrix w).contDiffAt hV).differentiableAt (by simp)
  have hDc := ((contDiffOn_chartCoordinates w).contDiffAt hV).differentiableAt (by simp)
  have hDs : DifferentiableAt ℝ S (C g.val) := (contDiff_chartSection_val w).differentiable (by simp) _
  have hprod := (hDu.hasFDerivAt.mul' (hDs.hasFDerivAt.comp g.val hDc.hasFDerivAt)).fderiv
  change fderiv ℝ (fun M => U M * S (C M)) g.val = _ at hprod
  rw [hI.fderiv_eq, fderiv_id] at hprod
  have h := DFunLike.congr_fun hprod Y
  change Y = U g.val * fderiv ℝ S (C g.val) (fderiv ℝ C g.val Y) +
     fderiv ℝ U g.val Y * S (C g.val) at h
  have hUb : U g.val = 1 := by rw [show U g.val = (chartUpper w g).val from chartUpperMatrix_val w g, hb, Units.val_one]
  have hCg : C g.val = z := hc
  rw [hUb, hCg, one_mul, add_comm] at h
  exact h.symm

set_option maxHeartbeats 850000 in
private theorem chartVector_linearization (w : Equiv.Perm (Fin n)) (z : Coordinates n) (A X : Mat n)
    (hA : A.IsUpperTriangular) (hFix : (chartSection w z).val * X = A * (chartSection w z).val) :
    fderiv ℝ (chartVector w X) z =
      (fderiv ℝ (chartCoordinates w) (chartSection w z).val).comp
        ((linearizedAction A X).comp (fderiv ℝ (fun q => (chartSection w q).val) z)) := by
  let S := fun q => (chartSection w q).val
  let C := chartCoordinates w
  let L := linearizedAction A X
  have hV : chartVector w X = fun q => fderiv ℝ C (S q) (L (S q)) := by
    funext q
    change fderiv ℝ C (S q) (S q * X) = fderiv ℝ C (S q) (S q * X - A * S q)
    rw [map_sub, coordDifferential_vertical w (chartSection w q) (chartSection_data w q).1 A hA, sub_zero]
  have hDf : ContDiffAt ℝ ∞ (fderiv ℝ C) (S z) :=
    ((contDiffOn_chartCoordinates w).fderiv_of_isOpen (isOpen_chartMatrixDomain w) (by simp)).contDiffAt
      ((isOpen_chartMatrixDomain w).mem_nhds (chartSection_data w z).1)
  have hS : DifferentiableAt ℝ S z := (contDiff_chartSection_val w).differentiable (by simp) z
  have hG := ((hDf.differentiableAt (by simp)).comp z hS)
  have hL := L.hasFDerivAt.comp z hS.hasFDerivAt
  have hl0 : L (S z) = 0 := sub_eq_zero.mpr hFix
  rw [hV]
  change fderiv ℝ (fun q => (fderiv ℝ C ∘ S) q ((⇑L ∘ S) q)) z = _
  rw [fderiv_clm_apply hG hL.differentiableAt, hL.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  simp [Function.comp_apply, hl0, C, L, S]

set_option maxHeartbeats 850000 in
private theorem chartVector_cube (w : Equiv.Perm (Fin n)) (z : Coordinates n) (A X : Mat n)
    (hA : A.IsUpperTriangular) (hA2 : A * A = 0) (hX2 : X * X = 0)
    (hFix : (chartSection w z).val * X = A * (chartSection w z).val) :
    fderiv ℝ (chartVector w X) z ^ 3 = 0 := by
  let g := chartSection w z
  let D := fderiv ℝ (chartCoordinates w) g.val
  let J := fderiv ℝ (fun q => (chartSection w q).val) z
  let L := linearizedAction A X
  let M := D.comp (L.comp J)
  have hIntertwine (Y : Mat n) : M (D Y) = D (L Y) := by
    let U := fderiv ℝ (chartUpperMatrix w) g.val Y
    have hU := upperDifferential_upper w g (chartSection_data w z).1 Y
    have hA' : (U * A - A * U).IsUpperTriangular := by
      intro i j hij
      rw [Matrix.sub_apply, hU.mul hA hij, hA.mul hU hij, sub_zero]
    have hY : U * g.val + J (D Y) = Y := gaussDifferential_factorization w z Y
    have he : L (U * g.val) = (U * A - A * U) * g.val := by
      change (U * g.val) * X - A * (U * g.val) = _
      rw [mul_assoc U g.val X, hFix, sub_mul, mul_assoc, mul_assoc]
    calc
      M (D Y) = D (L (U * g.val) + L (J (D Y))) := by
        change D (L (J (D Y))) = _
        rw [map_add, he, coordDifferential_vertical w g (chartSection_data w z).1 _ hA', zero_add]
      _ = D (L Y) := by rw [← map_add, hY]
  rw [chartVector_linearization w z A X hA hFix]
  change M ^ 3 = 0
  apply ContinuousLinearMap.ext
  intro v
  change M (M (M v)) = 0
  rw [show M v = D (L (J v)) from rfl, hIntertwine, hIntertwine, linearizedAction_cube A X hA2 hX2, map_zero]

/-- At a stabilizing upper direction, the coordinate and scalar terms vanish.
If the left and right stabilizing matrices are square-zero, the derivative of the
coordinate vector field is cube-zero. -/
def ComplexBruhatLinearizationStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData) (w : Equiv.Perm (Fin n)) (z : Coordinates n) (A X : Mat n),
    (∀ i j, j ≤ i → A i j = 0) → A * A = 0 → X * X = 0 →
    (chartSection w z).val * X = A * (chartSection w z).val →
    chartVector w X z = 0 ∧ chartScalar w ds X z = 0 ∧ fderiv ℝ (chartVector w X) z ^ 3 = 0

theorem complexBruhatLinearization : ComplexBruhatLinearizationStatement := by
  intro n ds w z A X hA hA2 hX2 hFix
  have hUpper : A.IsUpperTriangular := fun i j hij => hA i j hij.le
  refine ⟨?_, ?_, chartVector_cube w z A X hUpper hA2 hX2 hFix⟩
  · unfold chartVector
    rw [hFix, coordDifferential_vertical w (chartSection w z) (chartSection_data w z).1 A hUpper]
  · unfold chartScalar
    rw [hFix, scalarDifferential_vertical w ds z A hA]

end Langlands.Global.RankinSelbergGlobal.ComplexBruhatLinearization
