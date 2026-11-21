import Langlands.GroupScheme.CliffordSpin.AffineEquations

/-! # Unnormalized Clifford coordinates of even reflection products -/

noncomputable section

universe u

open scoped TensorProduct Matrix

namespace Langlands.GroupScheme.CliffordSpin

open CliffordAlgebra Langlands.QuadraticForm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V] [Invertible (2 : F)]
  {n : ℕ} (Q : QuadraticForm F V) (b : Module.Basis (Fin n) F V)
  {A : Type u} [CommRing A] [Algebra F A]

/-- The reversion norm before imposing the equation that it equals one. -/
def reversionNorm (x : A ⊗[F] CliffordAlgebra Q) : A ⊗[F] CliffordAlgebra Q :=
  TensorProduct.map LinearMap.id reverse x * x

omit [Invertible (2 : F)] in
@[simp] theorem reversionNorm_sub_one (x : A ⊗[F] CliffordAlgebra Q) :
    reversionNorm Q x - 1 = normDefect Q A x := rfl

omit [Invertible (2 : F)] in
private theorem tensorLinear_smul (T : CliffordAlgebra Q →ₗ[F] CliffordAlgebra Q)
    (a : A) (x : A ⊗[F] CliffordAlgebra Q) :
    TensorProduct.map LinearMap.id T (a • x) = a • TensorProduct.map LinearMap.id T x :=
  (TensorProduct.AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) T).map_smul a x

omit [Invertible (2 : F)] in
/-- Scaling by a coefficient scalar preserves the grading equation. -/
theorem gradeDefect_smul (a : A) (x : A ⊗[F] CliffordAlgebra Q) :
    gradeDefect Q A (a • x) = a • gradeDefect Q A x := by
  rw [gradeDefect, gradeDefect, smul_sub, tensorLinear_smul]

omit [Invertible (2 : F)] in
/-- Scaling by a coefficient scalar multiplies reversion norm by its square. -/
theorem reversionNorm_smul (a : A) (x : A ⊗[F] CliffordAlgebra Q) :
    reversionNorm Q (a • x) = a ^ 2 • reversionNorm Q x := by
  rw [reversionNorm, reversionNorm, tensorLinear_smul,
    smul_mul_smul_comm, pow_two]

omit [Invertible (2 : F)] in
/-- Scaling by a coefficient scalar preserves the vector intertwining equations. -/
theorem actionDefect_smul (a : A) (x : A ⊗[F] CliffordAlgebra Q) (g : GL (Fin n) A) (i : Fin n) :
    actionDefect Q b A (a • x) g i = a • actionDefect Q b A x g i := by
  rw [actionDefect, actionDefect, smul_sub, smul_mul_assoc, mul_smul_comm]

omit [Invertible (2 : F)] in
/-- Unnormalized reversion norm is natural under extension of the coefficients. -/
theorem tensorMap_reversionNorm {B : Type u} [CommRing B] [Algebra F B] (f : A →ₐ[F] B)
    (x : A ⊗[F] CliffordAlgebra Q) :
    tensorMap Q f (reversionNorm Q x) = reversionNorm Q (tensorMap Q f x) := by
  simpa only [← reversionNorm_sub_one, map_sub, map_one, sub_left_inj] using tensorMap_normDefect Q f x

private theorem toBaseChange_matrixAction_basis (g : GL (Fin n) A) (i : Fin n) :
    toBaseChange A Q (ι (Q.baseChange A) (matrixAction b A g (b.baseChange A i))) =
      ∑ j, ((g : Matrix (Fin n) (Fin n) A) j i) ⊗ₜ[F] ι Q (b j) := by
  have h : matrixAction b A g (b.baseChange A i) =
      ∑ j, ((g : Matrix (Fin n) (Fin n) A) j i) • b.baseChange A j := by
    change (Matrix.GeneralLinearGroup.toLin' (b.baseChange A) g).toLinearEquiv (b.baseChange A i) = _
    rw [Matrix.GeneralLinearGroup.toLin'_apply, Fintype.linearCombination_apply]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    simp [Matrix.mulVec, dotProduct, Module.Basis.repr_self, Finsupp.single_apply]
  rw [h, map_sum, map_sum]
  simp only [Module.Basis.baseChange_apply, toBaseChange_ι,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem actionDefect_eq_zero_iff (c : CliffordAlgebra (Q.baseChange A))
    (g : GL (Fin n) A) (i : Fin n) :
    actionDefect Q b A (toBaseChange A Q c) g i = 0 ↔
      c * ι (Q.baseChange A) (b.baseChange A i) =
        ι (Q.baseChange A) (matrixAction b A g (b.baseChange A i)) * c := by
  rw [← (equivBaseChange A Q).injective.eq_iff]
  change _ ↔ toBaseChange A Q (_ * _) = toBaseChange A Q (_ * _)
  rw [map_mul, map_mul, toBaseChange_matrixAction_basis Q b, Module.Basis.baseChange_apply,
    toBaseChange_ι, actionDefect, sub_eq_zero]

variable {K : Type u} [Field K] [Algebra F K]

local notation "qK" => Q.baseChange K

private theorem zero_actionDefect_iff (c : (CliffordAlgebra qK)ˣ) (g : GL (Fin n) K) :
    (∀ i, actionDefect Q b K (toBaseChange K Q (c : CliffordAlgebra qK)) g i = 0) ↔
      ∀ v, (c : CliffordAlgebra qK) * ι qK v * ↑c⁻¹ = ι qK (matrixAction b K g v) := by
  have h (v : K ⊗[F] V) : ((c : CliffordAlgebra qK) * ι qK v * ↑c⁻¹ =
      ι qK (matrixAction b K g v)) ↔
      (c : CliffordAlgebra qK) * ι qK v = ι qK (matrixAction b K g v) * c := by
    calc
      _ ↔ ((c : CliffordAlgebra qK) * ι qK v * ↑c⁻¹) * c =
          ι qK (matrixAction b K g v) * c := (Units.mul_left_inj c).symm
      _ ↔ _ := by rw [mul_assoc (↑c * ι qK v), Units.inv_mul, mul_one]
  simp_rw [h, actionDefect_eq_zero_iff Q b]
  constructor
  · intro hh v
    let u := (LinearMap.mulLeft K (c : CliffordAlgebra qK)).comp (ι qK)
    let w := (LinearMap.mulRight K (c : CliffordAlgebra qK)).comp
      ((ι qK).comp (matrixAction b K g).toLinearMap)
    exact DFunLike.congr_fun ((b.baseChange K).ext (f₁ := u) (f₂ := w) hh) v
  · exact fun hh i => hh (b.baseChange K i)

private theorem isometry_of_intertwines (c : (CliffordAlgebra qK)ˣ)
    (g : GL (Fin n) K) (h : ∀ v, (c : CliffordAlgebra qK) * ι qK v * ↑c⁻¹ =
      ι qK (matrixAction b K g v)) (v : K ⊗[F] V) :
    qK (matrixAction b K g v) = qK v := by
  let : Invertible (2 : K) := (Invertible.map (algebraMap F K) 2).copy 2 (map_ofNat _ _).symm
  apply (algebraMap K (CliffordAlgebra qK)).injective
  rw [← ι_sq_scalar, ← ι_sq_scalar, ← h v]
  calc
    _ = ↑c * (ι qK v * ι qK v) * ↑c⁻¹ := by
      rw [show (↑c * ι qK v * ↑c⁻¹) * (↑c * ι qK v * ↑c⁻¹) =
        ↑c * (ι qK v * ((↑c⁻¹ * ↑c) * ι qK v)) * ↑c⁻¹ by simp only [mul_assoc],
        Units.inv_mul, one_mul]
    _ = _ := by rw [ι_sq_scalar, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

/-- A pair with scalar reversion norm and determinant-one action determines an even
reflection word whose value is that scalar times a square. -/
theorem exists_even_reflectionWord_of_pair (hQ : (qK).polarBilin.Nondegenerate)
    (u : (K ⊗[F] CliffordAlgebra Q)ˣ) (g : GL (Fin n) K) (a : K)
    (hg : gradeDefect Q K u = 0) (hn : reversionNorm Q (u : K ⊗[F] CliffordAlgebra Q) = algebraMap K _ a)
    (hd : Matrix.GeneralLinearGroup.det g = 1) (ha : ∀ i, actionDefect Q b K u g i = 0) :
    ∃ (l : List {v : K ⊗[F] V // qK v ≠ 0}) (t : K),
      Even l.length ∧ t ≠ 0 ∧ reflectionWordValue qK l = a * t ^ 2 := by
  let : Invertible (2 : K) := (Invertible.map (algebraMap F K) 2).copy 2 (map_ofNat _ _).symm
  let : Module.Finite K (K ⊗[F] V) := Module.Finite.of_basis (b.baseChange K)
  let e := equivBaseChange K Q
  let c := Units.map e.symm.toMonoidHom u
  have hc : e (c : CliffordAlgebra qK) = u := e.apply_symm_apply _
  have hc' : toBaseChange K Q (c : CliffordAlgebra qK) = u := hc
  have hcG : involute (c : CliffordAlgebra qK) = c := e.injective (by
    rw [show e (involute (c : CliffordAlgebra qK)) = _ from toBaseChange_involute K Q c, hc', hc]
    exact sub_eq_zero.mp hg)
  have hcN : reverse (c : CliffordAlgebra qK) * c = algebraMap K _ a := e.injective (by
    rw [map_mul, show e (reverse (c : CliffordAlgebra qK)) = _ from toBaseChange_reverse K Q c, hc', hc,
      AlgEquiv.commutes]
    exact hn)
  have hact := (zero_actionDefect_iff Q b c g).mp (fun i => by
    change actionDefect Q b K (e (c : CliffordAlgebra qK)) g i = 0
    rw [hc]
    exact ha i)
  let f : (qK).IsometryEquiv qK := ⟨matrixAction b K g, isometry_of_intertwines Q b c g hact⟩
  have hf : f.toLinearEquiv.toLinearMap.det = 1 := by
    rw [← LinearEquiv.coe_det, show f.toLinearEquiv = matrixAction b K g from rfl,
      det_matrixAction, hd, Units.val_one]
  obtain ⟨l, hl, hfl⟩ := exists_even_reflectionWord qK hQ f hf
  obtain ⟨t, ht0, ht⟩ := exists_smul_of_even_clifford_conj_eq qK hQ (cliffordReflectionWord qK l) c
    (involute_cliffordReflectionWord_of_even qK l hl) hcG (fun v => by
      rw [cliffordReflectionWord_conj_of_even qK l hl, hfl, hact v]
      rfl)
  refine ⟨l, t, hl, ht0, (algebraMap K (CliffordAlgebra qK)).injective ?_⟩
  rw [mul_comm a, map_mul, ← Algebra.smul_def, ← hcN, pow_two,
    ← smul_mul_smul_comm, ← map_smul, ← ht]
  exact (reverse_mul_cliffordReflectionWord qK l).symm

/-- An even reflection word gives an even tensor unit with the expected scalar norm
and an intertwining determinant-one coefficient matrix. -/
theorem exists_pair_of_even_reflectionWord (l : List {v : K ⊗[F] V // qK v ≠ 0})
    (hl : Even l.length) :
    ∃ (u : (K ⊗[F] CliffordAlgebra Q)ˣ) (g : GL (Fin n) K),
      gradeDefect Q K u = 0 ∧
      reversionNorm Q (u : K ⊗[F] CliffordAlgebra Q) = algebraMap K _ (reflectionWordValue qK l) ∧
      Matrix.GeneralLinearGroup.det g = 1 ∧ ∀ i, actionDefect Q b K u g i = 0 := by
  let : Invertible (2 : K) := (Invertible.map (algebraMap F K) 2).copy 2 (map_ofNat _ _).symm
  let : Module.Finite K (K ⊗[F] V) := Module.Finite.of_basis (b.baseChange K)
  let c := cliffordReflectionWord qK l
  let f := (reflectionWord qK l).toLinearEquiv
  let g := (matrixAction b K).symm f
  have hg : matrixAction b K g = f := MulEquiv.apply_symm_apply _ _
  refine ⟨Units.map (toBaseChange K Q).toMonoidHom c, g, ?_, ?_, ?_, ?_⟩
  · change gradeDefect Q K (toBaseChange K Q (c : CliffordAlgebra qK)) = 0
    rw [gradeDefect, ← toBaseChange_involute, involute_cliffordReflectionWord_of_even qK l hl, sub_self]
  · change reversionNorm Q (toBaseChange K Q (c : CliffordAlgebra qK)) = _
    rw [reversionNorm, ← toBaseChange_reverse, ← map_mul, reverse_mul_cliffordReflectionWord,
      AlgHom.commutes]
    rfl
  · apply Units.ext
    rw [← det_matrixAction b, hg, LinearEquiv.coe_det]
    exact (det_reflectionWord qK l).trans hl.neg_one_pow
  · apply (zero_actionDefect_iff Q b c g).mpr
    intro v
    rw [cliffordReflectionWord_conj_of_even qK l hl, hg]
    rfl

end Langlands.GroupScheme.CliffordSpin
