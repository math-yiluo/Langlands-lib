import Langlands.GroupScheme.OddOrthogonalForm.QuadraticDescent
import Langlands.GroupScheme.Quaternionic.ScalarNormOneReindex
import Langlands.GroupScheme.Quaternionic.QuadraticValueExt

/-! # Regularity and polar defect of the descended odd scalar form -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped Matrix

namespace Langlands.GroupScheme.OddOrthogonalForm

open OddOrthogonalMatrix
open Quaternionic.FirstKindInvolution
open Quaternionic.ScalarNormOnePoints (finrank_ker_vecMulLinear)

section ScalarExtension

variable {K N : Type u} [Field K] [Field N] [Algebra K N]
  {i : Type} [Fintype i] [DecidableEq i]

omit [DecidableEq i] in
private theorem sesqForm_map (D : Matrix i i K) (x y : i → K) :
    (scalar N).sesqForm (D.map (algebraMap K N)) (algebraMap K N ∘ x) (algebraMap K N ∘ y) =
      algebraMap K N ((scalar K).sesqForm D x y) := by
  simp only [scalar_sesqForm, Function.comp_apply, Matrix.map_apply, _root_.map_sum, _root_.map_mul]

private theorem radicalFree_of_map (D : Matrix i i K)
    (hD : (scalar N).IsRadicalFreeQuadratic (Submodule.Quotient.mk (D.map (algebraMap K N)))) :
    (scalar K).IsRadicalFreeQuadratic (Submodule.Quotient.mk D) := by
  intro x hx hp
  let f := algebraMap K N
  have hx' : (scalar N).quadraticValue (f ∘ x) (Submodule.Quotient.mk (D.map f)) = 0 := by
    rw [scalar_quadraticValue_mk_eq_zero_iff, ← scalar_sesqForm, sesqForm_map]
    have h : (scalar K).sesqForm D x x = 0 := by
      simpa only [scalar_quadraticValue_mk_eq_zero_iff, scalar_sesqForm] using hx
    rw [h, _root_.map_zero]
  have hrow : x ᵥ* (D + Dᵀ) = 0 := by
    funext a
    have h := hp (Pi.single a 1)
    rwa [scalar_polar_mk, sesqForm_single_right, scalar_apply, mul_one] at h
  have hrow' : (f ∘ x) ᵥ* (D.map f + (D.map f)ᵀ) = 0 := by
    rw [← Matrix.transpose_map, ← Matrix.map_add _ (_root_.map_add f)]
    funext a
    rw [← RingHom.map_vecMul, hrow]
    exact _root_.map_zero f
  have hzero : f ∘ x = 0 := hD _ hx' (fun y => by
    rw [scalar_polar_mk, sesqForm_eq_dotProduct, Matrix.dotProduct_mulVec, hrow', zero_dotProduct])
  funext a
  exact f.injective ((congrFun hzero a).trans (_root_.map_zero f).symm)

private theorem rank_map_algebraMap (M : Matrix i i K) :
    (M.map (algebraMap K N)).rank = M.rank := by
  classical
  let f := algebraMap K N
  obtain ⟨V, U, e, hV, hU, h⟩ := M.exists_rank_normal_form
  let d : i → K := fun a => Sum.elim (fun _ => 1) (fun _ => 0) (e a)
  have hd : V * M * U = Matrix.diagonal d := by
    rw [h, ← Matrix.diagonal_one, ← Matrix.diagonal_zero, Matrix.fromBlocks_diagonal,
      Matrix.submatrix_diagonal_equiv]
    rfl
  have hVdet := (Matrix.isUnit_iff_isUnit_det V).mp hV
  have hUdet := (Matrix.isUnit_iff_isUnit_det U).mp hU
  have hK : (Matrix.diagonal d).rank = M.rank := by
    rw [← hd, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUdet,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hVdet]
  have hm := congrArg (fun A : Matrix i i K => A.map f) hd
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (_root_.map_zero f)] at hm
  change V.map f * M.map f * U.map f = Matrix.diagonal (f ∘ d) at hm
  have hN : (Matrix.diagonal (f ∘ d)).rank = (M.map f).rank := by
    have hV' : IsUnit (V.map f).det := (RingHom.map_det f V) ▸ hVdet.map f
    have hU' : IsUnit (U.map f).det := (RingHom.map_det f U) ▸ hUdet.map f
    rw [← hm, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hU',
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hV']
  rw [← hN, ← hK, Matrix.rank_diagonal, Matrix.rank_diagonal]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun a => not_congr f.map_eq_zero_iff)

end ScalarExtension

variable {K N : Type u} [Field K] [Field N] [Algebra K N] {n : ℕ}
variable {H : GroupScheme (Spec (CommRingCat.of K))}
  (φ : LocalGroupIso H (splitGroup K n) (ringTest K N)) [FiniteDimensional K N] [IsGalois K N]

/-- The scalar extension of the descended quadratic form to the splitting cover. -/
def descendedFormOverCover (hn : 2 ≤ n) : (scalar N).QuadraticForms (Index (Fin n)) :=
  Submodule.Quotient.mk ((descendedMatrix φ hn).map (algebraMap K N))

/-- Pullback by the Hilbert-90 basis gives the split scalar quadratic form. -/
theorem descendedFormOverCover_pullback (hn : 2 ≤ n) :
    (scalar N).quadraticPullback (descentBasis φ hn).val (descendedFormOverCover φ hn) =
      form (Fin n) N := by
  rw [descendedFormOverCover, quadraticPullback_mk, form, Submodule.Quotient.eq]
  obtain ⟨U, hU⟩ := descentBasis_congruence φ hn
  exact (mem_quadraticKernel_scalar _).2 ⟨U, hU.symm⟩

private theorem radicalFree_descendedFormOverCover (hn : 2 ≤ n) :
    (scalar N).IsRadicalFreeQuadratic (descendedFormOverCover φ hn) := by
  intro x hx hp
  let P := descentBasis φ hn
  let z := x ᵥ* P⁻¹.val
  have hz : z ᵥ* P.val = x := by
    dsimp only [z]
    rw [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]
  have hzero : z = 0 := by
    apply radicalFree_form
    · rw [← descendedFormOverCover_pullback φ hn, quadraticValue_quadraticPullback]
      exact hz.symm ▸ hx
    · intro y
      rw [← descendedFormOverCover_pullback φ hn, polar_quadraticPullback, sesqForm_gramPullback]
      exact hz.symm ▸ hp (y ᵥ* P.val)
  rw [← hz, hzero, Matrix.zero_vecMul]

/-- The ground-field quadratic form has zero quadratic radical. -/
theorem radicalFree_descendedForm (hn : 2 ≤ n) :
    (scalar K).IsRadicalFreeQuadratic (descendedForm φ hn) :=
  radicalFree_of_map (descendedMatrix φ hn) (radicalFree_descendedFormOverCover φ hn)

private theorem polar_descendedFormOverCover (hn : 2 ≤ n) :
    (scalar N).polar (descendedFormOverCover φ hn) =
      ((scalar K).polar (descendedForm φ hn)).map (algebraMap K N) := by
  rw [descendedFormOverCover, descendedForm, scalar_polar_mk, scalar_polar_mk,
    Matrix.map_add _ (_root_.map_add (algebraMap K N)), Matrix.transpose_map]

open Classical in
/-- The ground-field polar kernel has dimension one in characteristic two and zero elsewhere. -/
theorem finrank_polarKer_descendedForm (hn : 2 ≤ n) :
    Module.finrank K (LinearMap.ker ((scalar K).polar (descendedForm φ hn)).vecMulLinear) =
      (if (2 : K) = 0 then 1 else 0) := by
  let P := descentBasis φ hn
  let Q := (scalar N).polar (descendedFormOverCover φ hn)
  have hc : P.val * Q * P.valᵀ = (scalar N).polar (form (Fin n) N) := by
    have h := congrArg (scalar N).polar (descendedFormOverCover_pullback φ hn)
    rw [polar_quadraticPullback] at h
    exact h
  have hP : IsUnit P.val.det := (Matrix.isUnit_iff_isUnit_det P.val).mp P.isUnit
  have hPt : IsUnit P.valᵀ.det := by simpa only [Matrix.det_transpose] using hP
  have hr : ((scalar N).polar (form (Fin n) N)).rank =
      ((scalar K).polar (descendedForm φ hn)).rank := by
    rw [← hc, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hPt,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP]
    dsimp only [Q]
    rw [polar_descendedFormOverCover, rank_map_algebraMap]
  have hfin := finrank_polarKernel (l := Fin n) (K := N)
  rw [finrank_ker_vecMulLinear, hr] at hfin
  rw [finrank_ker_vecMulLinear]
  have h2 : (2 : N) = 0 ↔ (2 : K) = 0 := by
    rw [← _root_.map_ofNat (algebraMap K N) 2]
    exact (algebraMap K N).map_eq_zero_iff
  simpa only [h2] using hfin

end Langlands.GroupScheme.OddOrthogonalForm
