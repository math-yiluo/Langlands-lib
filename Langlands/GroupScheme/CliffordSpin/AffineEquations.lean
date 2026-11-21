import Langlands.LinearAlgebra.CliffordSpinLift
import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Affine coefficient equations for scalar Clifford spin lifts -/

noncomputable section

universe u

open scoped TensorProduct Matrix

namespace Langlands.GroupScheme.CliffordSpin

open CliffordAlgebra Langlands.QuadraticForm

variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V] [Invertible (2 : F)]
  {n : ℕ} (Q : QuadraticForm F V) (b : Module.Basis (Fin n) F V)
  (A : Type u) [CommRing A] [Algebra F A]

/-- The matrix action on the scalar-extended vector space in the chosen basis. -/
def matrixAction : GL (Fin n) A ≃* ((A ⊗[F] V) ≃ₗ[A] (A ⊗[F] V)) :=
  (Matrix.GeneralLinearGroup.toLin' (b.baseChange A)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[F] V))

/-- The ambient tensor unit and its matrix action written in Clifford and linear coordinates. -/
def pairEquiv : ((A ⊗[F] CliffordAlgebra Q)ˣ × GL (Fin n) A) ≃*
    ((CliffordAlgebra (Q.baseChange A))ˣ × ((A ⊗[F] V) ≃ₗ[A] (A ⊗[F] V))) :=
  (Units.mapEquiv (equivBaseChange A Q).symm.toMulEquiv).prodCongr (matrixAction b A)

/-- Spin lifts written as a subgroup in the tensor unit and matrix coordinates. -/
def coefficientSubgroup : Subgroup ((A ⊗[F] CliffordAlgebra Q)ˣ × GL (Fin n) A) :=
  (cliffordSpinLiftSubgroup (Q.baseChange A)).comap (pairEquiv Q b A).toMonoidHom

/-- The grade involution equation in the tensor algebra. -/
def gradeDefect (x : A ⊗[F] CliffordAlgebra Q) : A ⊗[F] CliffordAlgebra Q :=
  TensorProduct.map LinearMap.id involute.toLinearMap x - x

/-- The reversion-norm equation in the tensor algebra. -/
def normDefect (x : A ⊗[F] CliffordAlgebra Q) : A ⊗[F] CliffordAlgebra Q :=
  TensorProduct.map LinearMap.id reverse x * x - 1

/-- The intertwining equation for the `i`-th basis vector. -/
def actionDefect (x : A ⊗[F] CliffordAlgebra Q) (g : GL (Fin n) A) (i : Fin n) :
    A ⊗[F] CliffordAlgebra Q :=
  x * (1 ⊗ₜ[F] ι Q (b i)) - (∑ j, ((g : Matrix (Fin n) (Fin n) A) j i) ⊗ₜ[F] ι Q (b j)) * x

variable {A}

omit [Invertible (2 : F)] in
private theorem matrixAction_basis (g : GL (Fin n) A) (i : Fin n) :
    matrixAction b A g (b.baseChange A i) =
      ∑ j, ((g : Matrix (Fin n) (Fin n) A) j i) • b.baseChange A j := by
  change (Matrix.GeneralLinearGroup.toLin' (b.baseChange A) g).toLinearEquiv (b.baseChange A i) = _
  rw [Matrix.GeneralLinearGroup.toLin'_apply, Fintype.linearCombination_apply]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp [Matrix.mulVec, dotProduct, Module.Basis.repr_self, Finsupp.single_apply]

omit [Invertible (2 : F)] in
/-- The determinant of the basis action is the determinant of its coefficient matrix. -/
theorem det_matrixAction (g : GL (Fin n) A) :
    LinearEquiv.det (matrixAction b A g) = Matrix.GeneralLinearGroup.det g := by
  let B := b.baseChange A
  apply Units.ext
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix B]
  have h : LinearMap.toMatrix B B ((matrixAction b A g) : (A ⊗[F] V) →ₗ[A] A ⊗[F] V) = g := by
    ext j i
    rw [LinearMap.toMatrix_apply]
    change B.repr (matrixAction b A g (b.baseChange A i)) j = _
    rw [matrixAction_basis b]
    simp [B, Module.Basis.repr_self, Finsupp.single_apply]
  rw [h]
  rfl

private theorem toBaseChange_action_basis (g : GL (Fin n) A) (i : Fin n) :
    toBaseChange A Q (ι (Q.baseChange A) (matrixAction b A g (b.baseChange A i))) =
      ∑ j, ((g : Matrix (Fin n) (Fin n) A) j i) ⊗ₜ[F] ι Q (b j) := by
  rw [matrixAction_basis b, map_sum, map_sum]
  simp only [Module.Basis.baseChange_apply, toBaseChange_ι,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The tensor and matrix equations cut out exactly the Clifford coefficient subgroup. -/
theorem mem_coefficientSubgroup_iff (x : (A ⊗[F] CliffordAlgebra Q)ˣ) (g : GL (Fin n) A) :
    (x, g) ∈ coefficientSubgroup Q b A ↔ gradeDefect Q A x = 0 ∧ normDefect Q A x = 0 ∧
      Matrix.GeneralLinearGroup.det g = 1 ∧ ∀ i, actionDefect Q b A x g i = 0 := by
  let q := Q.baseChange A
  let c : CliffordAlgebra q := ofBaseChange A Q x
  let f := matrixAction b A g
  change (involute c = c ∧ reverse c * c = 1 ∧ LinearEquiv.det f = 1 ∧
    ∀ v : A ⊗[F] V, c * ι q v = ι q (f v) * c) ↔ _
  have hc : toBaseChange A Q c = (x : A ⊗[F] CliffordAlgebra Q) := toBaseChange_ofBaseChange A Q x
  let E := equivBaseChange A Q
  have hi : Function.Injective (toBaseChange A Q) := E.injective
  have hh : involute c = c ↔ gradeDefect Q A x = 0 := by
    rw [← hi.eq_iff, toBaseChange_involute, hc, gradeDefect, sub_eq_zero]
  have hn : reverse c * c = 1 ↔ normDefect Q A x = 0 := by
    calc
      _ ↔ toBaseChange A Q (reverse c * c) = toBaseChange A Q 1 := hi.eq_iff.symm
      _ ↔ _ := by rw [map_mul, map_one, toBaseChange_reverse, hc, normDefect, sub_eq_zero]
  have hact (i : Fin n) : c * ι q (b.baseChange A i) = ι q (f (b.baseChange A i)) * c ↔
      actionDefect Q b A x g i = 0 := by
    calc
      _ ↔ toBaseChange A Q (c * ι q (b.baseChange A i)) =
          toBaseChange A Q (ι q (f (b.baseChange A i)) * c) := hi.eq_iff.symm
      _ ↔ _ := by
        rw [map_mul, map_mul, hc, actionDefect, sub_eq_zero]
        change (x : A ⊗[F] CliffordAlgebra Q) * toBaseChange A Q (ι q (b.baseChange A i)) =
          toBaseChange A Q (ι q (matrixAction b A g (b.baseChange A i))) * x ↔ _
        rw [show toBaseChange A Q (ι q (matrixAction b A g (b.baseChange A i))) = _ from
          toBaseChange_action_basis Q b g i, Module.Basis.baseChange_apply]
        rw [show toBaseChange A Q (ι q (1 ⊗ₜ[F] b i)) = _ from toBaseChange_ι A Q 1 (b i)]
  rw [hh, hn, show LinearEquiv.det f = _ from det_matrixAction b g]
  apply and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · exact fun h i => (hact i).mp (h _)
  · intro h v
    let L := (LinearMap.mulLeft A c).comp (ι q)
    let R := (LinearMap.mulRight A c).comp ((ι q).comp f.toLinearMap)
    have hLR : L = R := (b.baseChange A).ext fun i => (hact i).mpr (h i)
    exact DFunLike.congr_fun hLR v

section Naturality

variable {B : Type u} [CommRing B] [Algebra F B] (φ : A →ₐ[F] B)

/-- The coefficient map on the base-extended Clifford algebra in tensor coordinates. -/
abbrev tensorMap : A ⊗[F] CliffordAlgebra Q →ₐ[F] B ⊗[F] CliffordAlgebra Q :=
  Algebra.TensorProduct.map φ (AlgHom.id F (CliffordAlgebra Q))

omit [Invertible (2 : F)] in
private theorem tensorMap_linearMap (T : CliffordAlgebra Q →ₗ[F] CliffordAlgebra Q)
    (x : A ⊗[F] CliffordAlgebra Q) :
    tensorMap Q φ (TensorProduct.map LinearMap.id T x) = TensorProduct.map LinearMap.id T (tensorMap Q φ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a c => simp
  | add x y hx hy => simp only [map_add, hx, hy]

omit [Invertible (2 : F)] in
/-- The grading defect is natural in the coefficient algebra. -/
theorem tensorMap_gradeDefect (x : A ⊗[F] CliffordAlgebra Q) :
    tensorMap Q φ (gradeDefect Q A x) = gradeDefect Q B (tensorMap Q φ x) := by
  rw [gradeDefect, gradeDefect, map_sub, tensorMap_linearMap]

omit [Invertible (2 : F)] in
/-- The norm defect is natural in the coefficient algebra. -/
theorem tensorMap_normDefect (x : A ⊗[F] CliffordAlgebra Q) :
    tensorMap Q φ (normDefect Q A x) = normDefect Q B (tensorMap Q φ x) := by
  rw [normDefect, normDefect, map_sub, map_mul, map_one, tensorMap_linearMap]

omit [Invertible (2 : F)] in
/-- The vector intertwining defects are natural in the coefficient algebra. -/
theorem tensorMap_actionDefect (x : A ⊗[F] CliffordAlgebra Q) (g : GL (Fin n) A) (i : Fin n) :
    tensorMap Q φ (actionDefect Q b A x g i) =
      actionDefect Q b B (tensorMap Q φ x) (Matrix.GeneralLinearGroup.map φ.toRingHom g) i := by
  simp [actionDefect, Matrix.GeneralLinearGroup.map_apply]

end Naturality

end Langlands.GroupScheme.CliffordSpin
