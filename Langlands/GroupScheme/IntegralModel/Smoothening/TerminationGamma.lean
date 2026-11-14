import Langlands.GroupScheme.IntegralModel.Smoothening.TerminationDilatation
import Langlands.GroupScheme.IntegralModel.Smoothening.TensorDensity
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # Quasi-regularity of `(ϖ, z)` from the integral points

Let `C` be a commutative bialgebra over a discrete valuation ring `R` with uniformizer `ϖ`, and let
`φ i` be a family of `R`-points of `C`. Let `z k` be elements whose values at all the points lie in
the maximal ideal, and whose differentials at the counit are dual to residue-field-valued forms
`l m`. If `ϖ b₀ + ∑ z_k b_k = 0`, then there is `h` with unit counit value such that all values of
`h b₀` and `h b_k` at the points lie in the maximal ideal.

The proof translates the relation by each point (right translation `c ↦ (id ⊗ φ) Δ c`) and takes
first-order parts. The differentials of the translated `z k` are the values at the point of a
matrix `H` with entries in `k ⊗ C`, so `h` is a lift of `det H`. -/

noncomputable section

universe u v

open scoped TensorProduct
open IsLocalRing Coalgebra Bialgebra

namespace Langlands.GroupScheme.IntegralModel.Smoothening.Termination

variable {R : Type u} [CommRing R] {C : Type v} [CommRing C] [Bialgebra R C]

/-- Right translation by an `R`-point. -/
def rtrans (φ : C →ₐ[R] R) : C →ₐ[R] C :=
  (Algebra.TensorProduct.rid R R C).toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id R C) φ).comp (comulAlgHom R C))

theorem rtrans_apply (φ : C →ₐ[R] R) (c : C) :
    rtrans φ c = Algebra.TensorProduct.rid R R C
      (Algebra.TensorProduct.map (AlgHom.id R C) φ (comul c)) := rfl

theorem counit_rtrans (φ : C →ₐ[R] R) (c : C) : counitAlgHom R C (rtrans φ c) = φ c := by
  have key : ∀ w : C ⊗[R] C, counitAlgHom R C (Algebra.TensorProduct.rid R R C
      (Algebra.TensorProduct.map (AlgHom.id R C) φ w)) =
      φ (TensorProduct.lid R C (counit.rTensor C w)) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul p q => simp [mul_comm]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, map_add, map_add]
  rw [rtrans_apply, key, rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]

theorem rtrans_counit (c : C) : rtrans (counitAlgHom R C) c = c := by
  have key : ∀ w : C ⊗[R] C, Algebra.TensorProduct.rid R R C
      (Algebra.TensorProduct.map (AlgHom.id R C) (counitAlgHom R C) w) =
      TensorProduct.rid R C (counit.lTensor C w) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul p q => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  rw [rtrans_apply, key, lTensor_counit_comul, TensorProduct.rid_tmul, one_smul]

section Local

variable [IsLocalRing R]

/-- Evaluation at an `R`-point of the base change of `C` to the residue field. -/
def evPt (φ : C →ₐ[R] R) : ResidueField R ⊗[R] C →ₐ[ResidueField R] ResidueField R :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) ((Algebra.ofId R (ResidueField R)).comp φ)
    (fun _ _ => .all _ _)

@[simp]
theorem evPt_tmul (φ : C →ₐ[R] R) (a : ResidueField R) (c : C) :
    evPt φ (a ⊗ₜ c) = a * algebraMap R (ResidueField R) (φ c) := by
  simp [evPt]

/-- The map `p ⊗ q ↦ l(dp) ⊗ q`. -/
def entryMap (l : Cot (counitAlgHom R C) →ₗ[R] ResidueField R) :
    C ⊗[R] C →ₗ[R] ResidueField R ⊗[R] C :=
  TensorProduct.map (l ∘ₗ dif (counitAlgHom R C)) LinearMap.id

theorem evPt_entryMap (φ : C →ₐ[R] R) (l : Cot (counitAlgHom R C) →ₗ[R] ResidueField R)
    (w : C ⊗[R] C) :
    evPt φ (entryMap l w) = l (dif (counitAlgHom R C) (Algebra.TensorProduct.rid R R C
      (Algebra.TensorProduct.map (AlgHom.id R C) φ w))) := by
  induction w using TensorProduct.inductionOn with
  | tmul p q =>
    rw [entryMap, TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.id_apply, evPt_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.rid_tmul, map_smul,
      map_smul, Algebra.smul_def, mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, map_add, map_add]

theorem l_dif_rtrans (φ : C →ₐ[R] R) (l : Cot (counitAlgHom R C) →ₗ[R] ResidueField R) (c : C) :
    l (dif (counitAlgHom R C) (rtrans φ c)) = evPt φ (entryMap l (comul c)) := by
  rw [evPt_entryMap, rtrans_apply]

end Local

section DVR

variable [IsDomain R] [IsDiscreteValuationRing R]

theorem algebraMap_residue_eq_zero {r : R} (hr : r ∈ maximalIdeal R) :
    algebraMap R (ResidueField R) r = 0 := by
  rw [IsLocalRing.ResidueField.algebraMap_eq, residue_eq_zero_iff]
  exact hr

/-- At a point where the translated differentials of the `z k` are independent, the values of the
coefficients of a relation `ϖ b₀ + ∑ z_k b_k = 0` lie in the maximal ideal. -/
theorem mem_maximalIdeal_of_det_ne_zero {ϖ : R} (hϖ : Irreducible ϖ) (ψ : C →ₐ[R] R) {c : ℕ}
    (z : Fin c → C) (hz : ∀ k, ψ (z k) ∈ maximalIdeal R)
    (l : Fin c → Cot (counitAlgHom R C) →ₗ[R] ResidueField R)
    (b0 : C) (b : Fin c → C) (hrel : ϖ • b0 + ∑ k, z k * b k = 0)
    (hdet : (Matrix.of fun k m => l m (dif (counitAlgHom R C) (rtrans ψ (z k)))).det ≠ 0) :
    ψ b0 ∈ maximalIdeal R ∧ ∀ k, ψ (b k) ∈ maximalIdeal R := by
  classical
  have hϖm : ϖ ∈ maximalIdeal R := (mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  have hzr : ∀ k, residue R (ψ (z k)) = 0 := fun k => (residue_eq_zero_iff _).mpr (hz k)
  have hϖr : residue R ϖ = 0 := (residue_eq_zero_iff _).mpr hϖm
  have hvec : Matrix.vecMul (fun k => residue R (ψ (b k)))
      (Matrix.of fun k m => l m (dif (counitAlgHom R C) (rtrans ψ (z k)))) = 0 := by
    funext m
    have h0 := congrArg (fun y => l m (dif (counitAlgHom R C) (rtrans ψ y))) hrel
    simp only [map_add, map_smul, map_sum, map_mul, dif_mul, counit_rtrans, map_zero] at h0
    simp only [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq, hzr, hϖr, zero_mul,
      zero_add] at h0
    simpa [Matrix.vecMul, dotProduct] using h0
  have hb : ∀ k, ψ (b k) ∈ maximalIdeal R := by
    by_contra hcon
    push Not at hcon
    obtain ⟨k, hk⟩ := hcon
    apply hdet
    rw [← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨_, ?_, hvec⟩
    intro hv
    apply hk
    have := congrFun hv k
    rw [Pi.zero_apply] at this
    rw [← residue_eq_zero_iff]
    exact this
  refine ⟨?_, hb⟩
  have h1 := congrArg ψ hrel
  rw [map_add, map_smul, map_sum, map_zero, smul_eq_mul] at h1
  have hm := hϖ.maximalIdeal_eq
  have hsum : ∑ k, ψ (z k * b k) ∈ Ideal.span {ϖ ^ 2} := by
    refine Ideal.sum_mem _ fun k _ => ?_
    rw [map_mul, pow_two, ← Ideal.span_singleton_mul_span_singleton]
    exact Ideal.mul_mem_mul (hm ▸ hz k) (hm ▸ hb k)
  have h2 : ϖ * ψ b0 ∈ Ideal.span {ϖ ^ 2} := by
    rw [eq_neg_of_add_eq_zero_left h1]
    exact Submodule.neg_mem _ hsum
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp h2
  rw [hm, Ideal.mem_span_singleton']
  refine ⟨t, ?_⟩
  apply mul_left_cancel₀ hϖ.ne_zero
  rw [← ht]
  ring

/-- **The Γ-trick.** Coefficients of a relation `ϖ b₀ + ∑ z_k b_k = 0` take values in the maximal
ideal at all points after multiplication by an element `h` with unit counit value. -/
theorem gamma_trick {ϖ : R} (hϖ : Irreducible ϖ) {ι : Type*} (φ : ι → C →ₐ[R] R) {c : ℕ}
    (z : Fin c → C) (hz : ∀ i k, φ i (z k) ∈ maximalIdeal R)
    (l : Fin c → Cot (counitAlgHom R C) →ₗ[R] ResidueField R)
    (hl : ∀ k m, l m (dif (counitAlgHom R C) (z k)) = if k = m then 1 else 0)
    (b0 : C) (b : Fin c → C) (hrel : ϖ • b0 + ∑ k, z k * b k = 0) :
    ∃ h : C, IsUnit (counitAlgHom R C h) ∧ (∀ i, φ i (h * b0) ∈ maximalIdeal R) ∧
      ∀ k i, φ i (h * b k) ∈ maximalIdeal R := by
  classical
  let H : Matrix (Fin c) (Fin c) (ResidueField R ⊗[R] C) :=
    Matrix.of fun k m => entryMap (l m) (comul (z k))
  obtain ⟨h, hh⟩ := exists_one_tmul_eq H.det
  have hev : ∀ ψ : C →ₐ[R] R, residue R (ψ h) =
      (Matrix.of fun k m => l m (dif (counitAlgHom R C) (rtrans ψ (z k)))).det := by
    intro ψ
    have h1 := congrArg (evPt ψ) hh
    rw [evPt_tmul, one_mul, AlgHom.map_det] at h1
    rw [← IsLocalRing.ResidueField.algebraMap_eq, h1]
    congr 1
    ext k m
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, H]
    rw [l_dif_rtrans]
  have hmem : ∀ i (x : C), (Matrix.of fun k m =>
      l m (dif (counitAlgHom R C) (rtrans (φ i) (z k)))).det = 0 → φ i (h * x) ∈ maximalIdeal R := by
    intro i x hd
    rw [map_mul]
    refine Ideal.mul_mem_right _ _ ?_
    rw [← residue_eq_zero_iff, hev, hd]
  refine ⟨h, ?_, ?_, ?_⟩
  · have h1 := hev (counitAlgHom R C)
    have hM : (Matrix.of fun k m =>
        l m (dif (counitAlgHom R C) (rtrans (counitAlgHom R C) (z k)))) = 1 := by
      ext k m
      simp only [Matrix.of_apply, rtrans_counit, hl, Matrix.one_apply]
    rw [hM, Matrix.det_one] at h1
    by_contra hu
    have : residue R (counitAlgHom R C h) = 0 :=
      (residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hu)
    rw [this] at h1
    exact zero_ne_one h1
  · intro i
    by_cases hd : (Matrix.of fun k m =>
        l m (dif (counitAlgHom R C) (rtrans (φ i) (z k)))).det = 0
    · exact hmem i b0 hd
    · rw [map_mul]
      exact Ideal.mul_mem_left _ _
        (mem_maximalIdeal_of_det_ne_zero hϖ (φ i) z (hz i) l b0 b hrel hd).1
  · intro k i
    by_cases hd : (Matrix.of fun k m =>
        l m (dif (counitAlgHom R C) (rtrans (φ i) (z k)))).det = 0
    · exact hmem i (b k) hd
    · rw [map_mul]
      exact Ideal.mul_mem_left _ _
        ((mem_maximalIdeal_of_det_ne_zero hϖ (φ i) z (hz i) l b0 b hrel hd).2 k)

end DVR

end Langlands.GroupScheme.IntegralModel.Smoothening.Termination
