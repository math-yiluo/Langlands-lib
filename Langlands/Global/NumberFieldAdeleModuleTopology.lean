import Langlands.Global.NumberFieldAdeleTensorComparison
import Langlands.Global.AdelicFunctoriality.Trace
import Langlands.Global.AdelicFunctoriality.IdeleNormLift
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! # Finite-free coordinates on the original full adele spaces -/

noncomputable section

universe u

open NumberField Module Topology
open scoped TensorProduct NumberField.LiesOver

namespace Langlands.Global

namespace AdelicFunctoriality

variable {K L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

/-- The full adelic trace is linear over the original full adele inclusion. -/
theorem adeleTrace_inclusion_mul (a : Adeles K) (y : Adeles L) :
    adeleTrace (adeleInclusion a * y) = a * adeleTrace y := by
  apply Prod.ext
  · funext p
    change (∑ q : InfinitePlacesAbove L p, InfiniteExtension.localTrace p q.1
      ((adeleInclusion a).1 q.1 * y.1 q.1)) =
      a.1 p * ∑ q : InfinitePlacesAbove L p, InfiniteExtension.localTrace p q.1 (y.1 q.1)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [adeleInclusion_infinite_apply, infiniteCompletionMap_comap_eq p q.1]
    change Algebra.trace p.Completion q.1.Completion
      (algebraMap p.Completion q.1.Completion (a.1 p) * y.1 q.1) = _
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
    rfl
  · exact finiteAdeleTrace_inclusion_mul a.2 y.2

end AdelicFunctoriality

open AdelicFunctoriality

variable (K L : Type u) [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)

/-- Algebraic coordinates obtained from the canonical full adelic tensor map. -/
def adeleBasisEquiv : Adeles L ≃+ (ι → Adeles K) :=
  (numberFieldAdeleTensorEquiv K L).symm.toAddEquiv.trans
    ((TensorProduct.equivFinsuppOfBasisLeft b).toAddEquiv.trans
      (Finsupp.linearEquivFunOnFinite K (Adeles K) ι).toAddEquiv)

@[simp] theorem adeleBasisEquiv_tensor (a : L) (x : Adeles K) (i : ι) :
    adeleBasisEquiv K L b (numberFieldAdeleTensorEquiv K L (a ⊗ₜ[K] x)) i =
      b.repr a i • x := by
  change (TensorProduct.equivFinsuppOfBasisLeft b)
    ((numberFieldAdeleTensorEquiv K L).symm
      (numberFieldAdeleTensorEquiv K L (a ⊗ₜ[K] x))) i = _
  rw [AlgEquiv.symm_apply_apply,
    TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]

/-- Every coordinate is the original continuous adelic trace against a
principal trace-dual basis element. -/
theorem adeleBasisEquiv_apply (y : Adeles L) (i : ι) :
    adeleBasisEquiv K L b y i =
      adeleTrace (algebraMap L (Adeles L) (b.traceDual i) * y) := by
  obtain ⟨z, rfl⟩ := (numberFieldAdeleTensorEquiv K L).surjective y
  induction z with
  | tmul a x =>
    rw [adeleBasisEquiv_tensor, numberFieldAdeleTensorEquiv_tmul,
      ← mul_assoc, ← map_mul, mul_comm _ (adeleInclusion x),
      adeleTrace_inclusion_mul, adeleTrace_principal]
    have ht : Algebra.trace K L (b.traceDual i * a) = b.repr a i := by
      have h := b.traceDual.traceDual_repr_apply a i
      rw [b.traceDual_traceDual] at h
      simpa only [Algebra.traceForm_apply, mul_comm] using h.symm
    rw [ht, Algebra.smul_def, mul_comm]
  | add z w hz hw =>
    simp only [map_add, Pi.add_apply, mul_add, hz, hw]

theorem continuous_adeleBasisEquiv : Continuous (adeleBasisEquiv K L b) := by
  apply continuous_pi
  intro i
  simp only [adeleBasisEquiv_apply]
  exact continuous_adeleTrace.comp (continuous_const.mul continuous_id)

/-- The inverse is the expected finite sum in the original upper-field adele ring. -/
theorem adeleBasisEquiv_symm_apply (x : ι → Adeles K) :
    (adeleBasisEquiv K L b).symm x =
      ∑ i, algebraMap L (Adeles L) (b i) * adeleInclusion (x i) := by
  change numberFieldAdeleTensorEquiv K L
    ((TensorProduct.equivFinsuppOfBasisLeft b).symm
      ((Finsupp.linearEquivFunOnFinite K (Adeles K) ι).symm x)) = _
  rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype]
  · simp only [map_sum, numberFieldAdeleTensorEquiv_tmul,
      Finsupp.linearEquivFunOnFinite_symm_apply]
  · intro i
    simp

theorem continuous_adeleBasisEquiv_symm :
    Continuous (adeleBasisEquiv K L b).symm := by
  change Continuous (fun x => (adeleBasisEquiv K L b).symm x)
  simp_rw [adeleBasisEquiv_symm_apply]
  exact continuous_finsetSum _ fun i _ =>
    continuous_const.mul (continuous_adeleInclusion.comp (continuous_apply i))

/-- The existing full adele topology is exactly the finite product topology
in any field basis, with explicit trace-dual inverse coordinates. -/
def adeleBasisHomeomorph : Adeles L ≃ₜ (ι → Adeles K) where
  toEquiv := (adeleBasisEquiv K L b).toEquiv
  continuous_toFun := continuous_adeleBasisEquiv K L b
  continuous_invFun := continuous_adeleBasisEquiv_symm K L b

end Langlands.Global
