import Langlands.Geometry.Analytic.ValuedField.TensorSeminorm
import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions
import Langlands.Analysis.UltrametricCompletion

/-! # The actual ultrametric projective completed tensor algebra -/

noncomputable section

universe u v w

open scoped TensorProduct NNReal

namespace Langlands.Analytic

namespace UltrametricTensorSeminorm

variable {K : Type u} [NormedField K]
  {A : Type v} [NormedCommRing A] [NormedAlgebra K A]
  {B : Type w} [NormedCommRing B] [NormedAlgebra K B]

/-- Scaling the left factors gives a representation of the scalar multiple. -/
def Representation.scaleLeft {t : A ⊗[K] B} (r : Representation K A B t) (c : K) :
    Representation K A B (c • t) where
  ι := r.ι
  left i := c • r.left i
  right := r.right
  sum_eq := by
    simp only [← TensorProduct.smul_tmul', ← Finset.smul_sum, r.sum_eq]

theorem Representation.value_scaleLeft_le {t : A ⊗[K] B}
    (r : Representation K A B t) (c : K) :
    (r.scaleLeft c).value ≤ ‖c‖₊ * r.value := by
  apply (Representation.value_le_iff _).mpr
  intro i
  change ‖c • r.left i‖₊ * ‖r.right i‖₊ ≤ ‖c‖₊ * r.value
  rw [nnnorm_smul, mul_assoc]
  exact mul_le_mul' (le_refl ‖c‖₊) (r.le_value i)

/-- The genuine finite-max/infimum projective seminorm respects scalar
multiplication with the coefficient field's original norm. -/
theorem seminormFun_smul_le (c : K) (t : A ⊗[K] B) :
    seminormFun (c • t) ≤ ‖c‖₊ * seminormFun t :=
  NNReal.le_mul_iInf fun r =>
    (seminormFun_le (r.scaleLeft c)).trans (r.value_scaleLeft_le c)

end UltrametricTensorSeminorm

namespace CompletedTensorAlgebra

variable (K : Type u) [NormedField K]
  (A : Type v) [NormedCommRing A] [NormedAlgebra K A]
  (B : Type w) [NormedCommRing B] [NormedAlgebra K B]

/-- The algebraic tensor, with a separate type identity so that its
projective seminorm does not change any ambient tensor-product instances. -/
def Algebraic := A ⊗[K] B

instance : CommRing (Algebraic K A B) :=
  inferInstanceAs (CommRing (A ⊗[K] B))

instance : Algebra K (Algebraic K A B) :=
  inferInstanceAs (Algebra K (A ⊗[K] B))

instance : SeminormedCommRing (Algebraic K A B) where
  __ := (ultrametricTensorSeminorm K A B).toSeminormedRing
  __ : CommRing (Algebraic K A B) := inferInstance

@[simp]
theorem norm_algebraic (t : Algebraic K A B) :
    ‖t‖ = ultrametricTensorSeminorm K A B t := rfl

instance : NormedAlgebra K (Algebraic K A B) where
  toAlgebra := (inferInstance : _root_.Algebra K (Algebraic K A B))
  norm_smul_le c t := by
    change ultrametricTensorSeminorm K A B (c • t) ≤
      ‖c‖ * ultrametricTensorSeminorm K A B t
    exact_mod_cast UltrametricTensorSeminorm.seminormFun_smul_le c t

instance : IsUltrametricDist (Algebraic K A B) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    (fun x y => isNonarchimedean_ultrametricTensorSeminorm x y)

instance : IsUniformAddGroup (Algebraic K A B) :=
  SeminormedAddCommGroup.to_isUniformAddGroup

instance : IsTopologicalRing (Algebraic K A B) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

instance : IsBoundedSMul K (Algebraic K A B) :=
  NormedSpace.toIsBoundedSMul

instance : UniformContinuousConstSMul K (Algebraic K A B) :=
  IsBoundedSMul.toUniformContinuousConstSMul

/-- The actual Hausdorff completion of the algebraic tensor equipped with
the finite-max/infimum projective seminorm. -/
def Algebra := UniformSpace.Completion (Algebraic K A B)

instance : NormedCommRing (Algebra K A B) :=
  inferInstanceAs (NormedCommRing (UniformSpace.Completion (Algebraic K A B)))

instance : NormedAlgebra K (Algebra K A B) :=
  inferInstanceAs (NormedAlgebra K (UniformSpace.Completion (Algebraic K A B)))

instance : CompleteSpace (Algebra K A B) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion (Algebraic K A B)))

instance : IsUltrametricDist (Algebra K A B) :=
  inferInstanceAs (IsUltrametricDist (UniformSpace.Completion (Algebraic K A B)))

/-- The actual dense algebra map to the Hausdorff completion. It need not
be injective when the algebraic projective seminorm has a kernel. -/
def toCompletion : Algebraic K A B →ₐ[K] Algebra K A B where
  __ := UniformSpace.Completion.coeRingHom
  commutes' c := (UniformSpace.Completion.algebraMap_def (Algebraic K A B) K c).symm

theorem denseRange_toCompletion : DenseRange (toCompletion K A B) :=
  UniformSpace.Completion.denseRange_coe

/-- On every algebraic tensor the norm is exactly the specified
finite-max/infimum projective seminorm, including its possible kernel. -/
@[simp]
theorem norm_toCompletion (t : Algebraic K A B) :
    ‖toCompletion K A B t‖ = ultrametricTensorSeminorm K A B t :=
  UniformSpace.Completion.norm_coe t

/-- The original first algebra maps by `a` to the completed pure tensor
`a ⊗ 1`; its bound permits a zero or non-normalized second algebra. -/
def leftMap : BoundedAlgHom K A (Algebra K A B) where
  toAlgHom := (toCompletion K A B).comp
    (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B)
  bounded := ⟨‖(1 : B)‖ + 1, by positivity, fun a => by
    change ‖toCompletion K A B (a ⊗ₜ[K] (1 : B))‖ ≤ (‖(1 : B)‖ + 1) * ‖a‖
    have h := ultrametricTensorSeminorm_tmul_le (E := K) a (1 : B)
    exact (norm_toCompletion K A B (a ⊗ₜ[K] (1 : B))).trans_le
      (h.trans (by nlinarith [norm_nonneg a]))⟩

/-- The original second algebra maps by `b` to the completed pure tensor
`1 ⊗ b`, with its actual norm estimate. -/
def rightMap : BoundedAlgHom K B (Algebra K A B) where
  toAlgHom := (toCompletion K A B).comp Algebra.TensorProduct.includeRight
  bounded := ⟨‖(1 : A)‖ + 1, by positivity, fun b => by
    change ‖toCompletion K A B ((1 : A) ⊗ₜ[K] b)‖ ≤ (‖(1 : A)‖ + 1) * ‖b‖
    have h := ultrametricTensorSeminorm_tmul_le (E := K) (1 : A) b
    exact (norm_toCompletion K A B ((1 : A) ⊗ₜ[K] b)).trans_le
      (h.trans (by nlinarith [norm_nonneg b]))⟩

theorem norm_leftMap_le (a : A) :
    ‖leftMap K A B a‖ ≤ ‖a‖ * ‖(1 : B)‖ := by
  change ‖toCompletion K A B (a ⊗ₜ[K] (1 : B))‖ ≤ _
  exact (norm_toCompletion K A B (a ⊗ₜ[K] (1 : B))).trans_le
    (ultrametricTensorSeminorm_tmul_le (E := K) a (1 : B))

theorem norm_rightMap_le (b : B) :
    ‖rightMap K A B b‖ ≤ ‖(1 : A)‖ * ‖b‖ := by
  change ‖toCompletion K A B ((1 : A) ⊗ₜ[K] b)‖ ≤ _
  exact (norm_toCompletion K A B ((1 : A) ⊗ₜ[K] b)).trans_le
    (ultrametricTensorSeminorm_tmul_le (E := K) (1 : A) b)

/-- Completed pure tensors are the products of the two actual algebra legs. -/
theorem toCompletion_tmul (a : A) (b : B) :
    toCompletion K A B (a ⊗ₜ[K] b) = leftMap K A B a * rightMap K A B b := by
  change toCompletion K A B (a ⊗ₜ[K] b) =
    toCompletion K A B (a ⊗ₜ[K] (1 : B)) *
      toCompletion K A B ((1 : A) ⊗ₜ[K] b)
  have h : (a ⊗ₜ[K] b) = (a ⊗ₜ[K] (1 : B)) * ((1 : A) ⊗ₜ[K] b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  exact (congrArg (toCompletion K A B) h).trans
    ((toCompletion K A B).map_mul _ _)

end CompletedTensorAlgebra
end Langlands.Analytic
