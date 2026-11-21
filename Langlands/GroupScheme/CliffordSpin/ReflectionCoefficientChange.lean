import Langlands.GroupScheme.CliffordSpin.AffineEquations
import Langlands.LinearAlgebra.CliffordUnitReflections

/-! # Reflections in unit-valued vectors in coefficient matrices -/

noncomputable section

universe u

open scoped TensorProduct Matrix

namespace Langlands.GroupScheme.CliffordSpin

open Langlands.QuadraticForm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section Reflection

variable {R W : Type u} [CommRing R] [AddCommGroup W] [Module R W]
  (D : QuadraticForm R W)

/-- Reflection along a vector whose value is equipped with a multiplicative inverse. -/
def reflectionOfUnit (v : W) (a : Rˣ) (ha : D v = (a : R)) : W ≃ₗ[R] W :=
  let d : QuadraticForm R W := ((a⁻¹ : Rˣ) : R) • D
  unitReflection d v (by
    change ((a⁻¹ : Rˣ) : R) * D v = 1
    rw [ha, Units.inv_mul])

private theorem reflectionOfUnit_apply (v : W) (a : Rˣ) (ha : D v = (a : R)) (x : W) :
    reflectionOfUnit D v a ha x = x - (((a⁻¹ : Rˣ) : R) * QuadraticMap.polar D v x) • v := by
  rw [reflectionOfUnit, unitReflection_apply]
  have h : QuadraticMap.polar (⇑(((a⁻¹ : Rˣ) : R) • D)) v x =
      ((a⁻¹ : Rˣ) : R) * QuadraticMap.polar D v x :=
    QuadraticMap.polar_smul (⇑D) _ _ _
  rw [h]

/-- A reflection along a unit-valued vector preserves the original form. -/
theorem reflectionOfUnit_preserves (v : W) (a : Rˣ) (ha : D v = (a : R)) (x : W) :
    D (reflectionOfUnit D v a ha x) = D x := by
  rw [reflectionOfUnit_apply, sub_eq_add_neg, QuadraticMap.map_add (⇑D), D.map_neg,
    D.map_smul, QuadraticMap.polar_neg_right, QuadraticMap.polar_smul_right,
    QuadraticMap.polar_comm D x v, ha, smul_eq_mul, smul_eq_mul]
  have h (c : R) : (((a⁻¹ : Rˣ) : R) * c) * (((a⁻¹ : Rˣ) : R) * c) * (a : R) =
      (((a⁻¹ : Rˣ) : R) * c) * c := by
    calc
      _ = (((a⁻¹ : Rˣ) : R) * (a : R)) * (((a⁻¹ : Rˣ) : R) * c) * c := by ring
      _ = _ := by rw [Units.inv_mul, one_mul]
  rw [h, ← sub_eq_add_neg, add_sub_cancel_right]

/-- The determinant of a reflection along a unit-valued vector is minus one. -/
theorem det_reflectionOfUnit {ι : Type} [Fintype ι] [DecidableEq ι] (c : Module.Basis ι R W)
    (v : W) (a : Rˣ) (ha : D v = (a : R)) : LinearEquiv.det (reflectionOfUnit D v a ha) = -1 :=
  det_unitReflection (((a⁻¹ : Rˣ) : R) • D) c v (by
    change ((a⁻¹ : Rˣ) : R) * D v = 1
    rw [ha, Units.inv_mul])

/-- The square of a reflection along a unit-valued vector is the identity. -/
theorem reflectionOfUnit_mul_self (v : W) (a : Rˣ) (ha : D v = (a : R)) :
    reflectionOfUnit D v a ha * reflectionOfUnit D v a ha = 1 := by
  apply LinearEquiv.ext
  intro x
  change reflectionOfUnit D v a ha (reflectionOfUnit D v a ha x) = x
  exact (reflectionOfUnit D v a ha).symm_apply_apply x

end Reflection

section FieldReflection

variable {k U : Type u} [Field k] [AddCommGroup U] [Module k U] (q : QuadraticForm k U)

/-- Over a field a unit-valued reflection is the reflection of Cartan–Dieudonné. -/
theorem reflectionOfUnit_eq_field_reflection (v : U) (a : kˣ) (ha : q v = (a : k)) :
    reflectionOfUnit q v a ha = (reflection q v (ha.trans_ne a.ne_zero)).toLinearEquiv := by
  apply LinearEquiv.ext
  intro x
  change reflectionOfUnit q v a ha x = reflection q v (ha.trans_ne a.ne_zero) x
  rw [reflectionOfUnit_apply, reflection_apply, QuadraticMap.polar_comm q v x, div_eq_mul_inv,
    ha, Units.val_inv_eq_inv_val, mul_comm ((a : k)⁻¹)]

end FieldReflection

section Coefficients

variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
  {n : ℕ} (b : Module.Basis (Fin n) F V)
  {A B : Type u} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]

/-- Change the coefficients in the left factor of a tensor vector. -/
abbrev changeVectorCoefficients (φ : A →ₐ[F] B) : A ⊗[F] V →ₗ[F] B ⊗[F] V :=
  TensorProduct.map φ.toLinearMap LinearMap.id

/-- Coefficient change is compatible with coefficient scalars. -/
theorem changeVectorCoefficients_smul (φ : A →ₐ[F] B) (a : A) (x : A ⊗[F] V) :
    changeVectorCoefficients φ (a • x) = φ a • changeVectorCoefficients φ x := by
  induction x using TensorProduct.inductionOn with
  | tmul t v => simp [TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- Successive changes of coefficients agree with their composite. -/
theorem changeVectorCoefficients_comp {C : Type u} [CommRing C] [Algebra F C]
    (φ : A →ₐ[F] B) (ψ : B →ₐ[F] C) (v : A ⊗[F] V) :
    changeVectorCoefficients ψ (changeVectorCoefficients φ v) = changeVectorCoefficients (ψ.comp φ) v := by
  induction v using TensorProduct.inductionOn with
  | tmul a v => rfl
  | add v w hv hw => simp only [map_add, hv, hw]

private theorem repr_changeVectorCoefficients (φ : A →ₐ[F] B) (x : A ⊗[F] V) (i : Fin n) :
    (b.baseChange B).repr (changeVectorCoefficients φ x) i = φ ((b.baseChange A).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x => simp [Algebra.smul_def, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

variable [Invertible (2 : F)] (Q : QuadraticForm F V)

/-- Polar pairings commute with maps of coefficient algebras. -/
theorem polar_changeVectorCoefficients (φ : A →ₐ[F] B) (x y : A ⊗[F] V) :
    QuadraticMap.polar (Q.baseChange B) (changeVectorCoefficients φ x) (changeVectorCoefficients φ y) =
      φ (QuadraticMap.polar (Q.baseChange A) x y) := by
  let : Invertible (2 : A) := (Invertible.map (algebraMap F A) 2).copy 2 (map_ofNat _ _).symm
  let : Invertible (2 : B) := (Invertible.map (algebraMap F B) 2).copy 2 (map_ofNat _ _).symm
  change (Q.baseChange B).polarBilin (changeVectorCoefficients φ x) (changeVectorCoefficients φ y) =
    φ ((Q.baseChange A).polarBilin x y)
  rw [QuadraticForm.polarBilin_baseChange, QuadraticForm.polarBilin_baseChange]
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul a v =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul c w => simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
        LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def, map_mul, AlgHom.commutes]

/-- Quadratic values commute with maps of coefficient algebras. -/
theorem quadratic_changeVectorCoefficients (φ : A →ₐ[F] B) (x : A ⊗[F] V) :
    Q.baseChange B (changeVectorCoefficients φ x) = φ (Q.baseChange A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a v => simp [Algebra.smul_def, AlgHom.commutes]
  | add x y hx hy =>
    rw [map_add, QuadraticMap.map_add (⇑(Q.baseChange B)), QuadraticMap.map_add (⇑(Q.baseChange A)),
      polar_changeVectorCoefficients Q φ, hx, hy, map_add, map_add]

/-- The coefficient matrix of a reflection along a vector of unit value. -/
def reflectionMatrix (v : A ⊗[F] V) (a : Aˣ) (ha : Q.baseChange A v = (a : A)) : GL (Fin n) A :=
  (matrixAction b A).symm (reflectionOfUnit (Q.baseChange A) v a ha)

@[simp] theorem matrixAction_reflectionMatrix (v : A ⊗[F] V) (a : Aˣ)
    (ha : Q.baseChange A v = (a : A)) :
    matrixAction b A (reflectionMatrix b Q v a ha) = reflectionOfUnit (Q.baseChange A) v a ha :=
  MulEquiv.apply_symm_apply _ _

omit [Invertible (2 : F)] in
private theorem matrixAction_repr (g : GL (Fin n) A) (i j : Fin n) :
    (b.baseChange A).repr (matrixAction b A g (b.baseChange A j)) i =
      (g : Matrix (Fin n) (Fin n) A) i j := by
  have h : matrixAction b A g (b.baseChange A j) =
      ∑ t, ((g : Matrix (Fin n) (Fin n) A) t j) • b.baseChange A t := by
    change (Matrix.GeneralLinearGroup.toLin' (b.baseChange A) g).toLinearEquiv (b.baseChange A j) = _
    rw [Matrix.GeneralLinearGroup.toLin'_apply, Fintype.linearCombination_apply]
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    simp [Matrix.mulVec, dotProduct, Module.Basis.repr_self, Finsupp.single_apply]
  rw [h, map_sum]
  simp [Module.Basis.repr_self, Finsupp.single_apply]

private theorem reflectionMatrix_apply (v : A ⊗[F] V) (a : Aˣ)
    (ha : Q.baseChange A v = (a : A)) (i j : Fin n) :
    (reflectionMatrix b Q v a ha : Matrix (Fin n) (Fin n) A) i j =
      (if j = i then 1 else 0) - (((a⁻¹ : Aˣ) : A) *
        QuadraticMap.polar (Q.baseChange A) v (b.baseChange A j)) * (b.baseChange A).repr v i := by
  rw [← matrixAction_repr b, matrixAction_reflectionMatrix, reflectionOfUnit_apply,
    map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, Module.Basis.repr_self,
    Finsupp.single_apply, smul_eq_mul]

/-- The reflection matrix specializes along any map of commutative coefficient algebras. -/
theorem map_reflectionMatrix (φ : A →ₐ[F] B) (v : A ⊗[F] V) (a : Aˣ)
    (ha : Q.baseChange A v = (a : A)) :
    Matrix.GeneralLinearGroup.map φ.toRingHom (reflectionMatrix b Q v a ha) =
      reflectionMatrix b Q (changeVectorCoefficients φ v) (Units.map φ.toMonoidHom a)
        ((quadratic_changeVectorCoefficients Q φ v).trans (congrArg φ ha)) := by
  apply Units.ext
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, reflectionMatrix_apply, reflectionMatrix_apply,
    map_sub, map_mul, map_mul, repr_changeVectorCoefficients]
  have hj : changeVectorCoefficients φ (b.baseChange A j) = b.baseChange B j := by
    rw [Module.Basis.baseChange_apply, Module.Basis.baseChange_apply, TensorProduct.map_tmul,
      AlgHom.toLinearMap_apply, LinearMap.id_apply, map_one]
  rw [← hj, polar_changeVectorCoefficients, ← map_inv (Units.map φ.toMonoidHom)]
  split_ifs <;> simp only [map_one, map_zero] <;> rfl

end Coefficients

end Langlands.GroupScheme.CliffordSpin
