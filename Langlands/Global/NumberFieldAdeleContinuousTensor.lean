import Langlands.Global.NumberFieldAdeleModuleTopology
import Mathlib.Topology.ContinuousMap.Algebra

/-! # Full adelic scalar extension of continuous functions -/

noncomputable section

universe u

open NumberField Module
open scoped TensorProduct

namespace Langlands.Global

variable (K L : Type u) [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

/-- The original full adelic inclusion as a base-field algebra map. -/
def adeleInclusionAlgHom :
    letI : Algebra K (Adeles L) :=
      ((algebraMap L (Adeles L)).comp (algebraMap K L)).toAlgebra
    Adeles K →ₐ[K] Adeles L := by
  letI : Algebra K (Adeles L) :=
    ((algebraMap L (Adeles L)).comp (algebraMap K L)).toAlgebra
  exact { AdelicFunctoriality.adeleInclusion with
    commutes' := AdelicFunctoriality.adeleInclusion_diagonal }

variable (X : Type*) [TopologicalSpace X]

/-- Extend each continuous base-adele-valued function by the original inclusion. -/
def adeleContinuousMapTensorAlgHom : L ⊗[K] C(X, Adeles K) →ₐ[L] C(X, Adeles L) := by
  letI : Algebra K (Adeles L) :=
    ((algebraMap L (Adeles L)).comp (algebraMap K L)).toAlgebra
  letI : IsScalarTower K L (Adeles L) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact AlgHom.liftEquiv K L C(X, Adeles K) C(X, Adeles L)
    (AlgHom.compLeftContinuous K (adeleInclusionAlgHom K L)
      AdelicFunctoriality.continuous_adeleInclusion)

@[simp] theorem adeleContinuousMapTensorAlgHom_tmul
    (a : L) (f : C(X, Adeles K)) (x : X) :
    adeleContinuousMapTensorAlgHom K L X (a ⊗ₜ[K] f) x =
      algebraMap L (Adeles L) a * AdelicFunctoriality.adeleInclusion (f x) := by
  change a • AdelicFunctoriality.adeleInclusion (f x) = _
  exact Algebra.smul_def _ _

/-- Evaluation is exactly tensor extension of evaluation followed by the
original canonical full-adele tensor map. -/
theorem eval_comp_adeleContinuousMapTensorAlgHom (x : X) :
    (ContinuousMap.evalAlgHom L (Adeles L) x).comp
        (adeleContinuousMapTensorAlgHom K L X) =
      (numberFieldAdeleTensorEquiv K L).toAlgHom.comp
        (Algebra.TensorProduct.lTensor L
          (ContinuousMap.evalAlgHom K (Adeles K) x)) := by
  apply AlgHom.ext
  intro z
  induction z with
  | tmul a f =>
    change adeleContinuousMapTensorAlgHom K L X (a ⊗ₜ[K] f) x =
      numberFieldAdeleTensorEquiv K L (a ⊗ₜ[K] f x)
    rw [adeleContinuousMapTensorAlgHom_tmul, numberFieldAdeleTensorEquiv_tmul]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- Full adelic scalar extension commutes with continuous functions on any space. -/
theorem adeleContinuousMapTensorAlgHom_bijective :
    Function.Bijective (adeleContinuousMapTensorAlgHom K L X) := by
  classical
  let b := Module.Free.chooseBasis K L
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := C(X, Adeles K)) b
  have hcoord (z : L ⊗[K] C(X, Adeles K)) (x : X) (i : Module.Free.ChooseBasisIndex K L) :
      adeleBasisEquiv K L b (adeleContinuousMapTensorAlgHom K L X z x) i = e z i x := by
    induction z with
    | tmul a f =>
      rw [adeleContinuousMapTensorAlgHom_tmul]
      change adeleBasisEquiv K L b (numberFieldAdeleTensorEquiv K L
        (a ⊗ₜ[K] f x)) i = _
      rw [adeleBasisEquiv_tensor]
      simp [e]
    | add z w hz hw =>
      simp only [map_add, ContinuousMap.add_apply, Pi.add_apply, Finsupp.add_apply, hz, hw]
  constructor
  · intro z w hzw
    apply e.injective
    ext i x
    rw [← hcoord, ← hcoord, hzw]
  · intro f
    let c : Module.Free.ChooseBasisIndex K L → C(X, Adeles K) := fun i =>
      ⟨fun x => adeleBasisEquiv K L b (f x) i,
        (continuous_apply i).comp ((continuous_adeleBasisEquiv K L b).comp f.continuous)⟩
    refine ⟨∑ i, b i ⊗ₜ[K] c i, ?_⟩
    ext x
    change adeleContinuousMapTensorAlgHom K L X (∑ i, b i ⊗ₜ[K] c i) x = f x
    simp only [map_sum, ContinuousMap.sum_apply, adeleContinuousMapTensorAlgHom_tmul]
    exact (adeleBasisEquiv_symm_apply K L b (adeleBasisEquiv K L b (f x))).symm.trans
      ((adeleBasisEquiv K L b).symm_apply_apply (f x))

/-- The comparison has precisely the original canonical formula on pure tensors. -/
def adeleContinuousMapTensorAlgEquiv : L ⊗[K] C(X, Adeles K) ≃ₐ[L] C(X, Adeles L) :=
  AlgEquiv.ofBijective (adeleContinuousMapTensorAlgHom K L X)
    (adeleContinuousMapTensorAlgHom_bijective K L X)

@[simp] theorem adeleContinuousMapTensorAlgEquiv_apply
    (z : L ⊗[K] C(X, Adeles K)) :
    adeleContinuousMapTensorAlgEquiv K L X z = adeleContinuousMapTensorAlgHom K L X z := rfl

end Langlands.Global
