import Langlands.Algebra.IdealLocalFlatnessCriterionStatement
import Langlands.Algebra.LocalFlatnessCriterion
import Langlands.Algebra.IdealTensorRelation
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! # The ideal variant of the local flatness criterion -/

universe u v w

open scoped TensorProduct
open TensorProduct

namespace Langlands.Algebra

section TensorReduction

variable {R : Type u} {M : Type w} [CommRing R] [AddCommGroup M] [Module R M]

private theorem tmul_mem_inclusion_range (I J : Ideal R) (hIJ : I ≤ J)
    (f : J) {x : M} (hx : x ∈ I • (⊤ : Submodule R M)) :
    f ⊗ₜ[R] x ∈ LinearMap.range ((Submodule.inclusion hIJ).rTensor M) := by
  refine Submodule.smul_induction_on hx (fun r hr x _ => ?_) (fun x y hx hy => ?_)
  ·
    refine ⟨(⟨r, hr⟩ : I) ⊗ₜ[R] ((f : R) • x), ?_⟩
    simp only [LinearMap.rTensor_tmul]
    rw [← smul_tmul, ← smul_tmul]
    congr 1
    apply Subtype.ext
    exact mul_comm _ _
  ·
    rw [tmul_add]
    exact add_mem hx hy

private theorem tensor_kernel_mem_inclusion_range (I J : Ideal R) (hIJ : I ≤ J)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M)]
    (z : J ⊗[R] M) (hz : J.subtype.rTensor M z = 0) :
    z ∈ LinearMap.range ((Submodule.inclusion hIJ).rTensor M) := by
  classical
  obtain ⟨n, f, x, rfl⟩ := exists_sum_tmul_eq z
  have hzero : ∑ i, (f i : R) • x i = 0 := by
    simpa using congrArg (TensorProduct.lid R M) hz
  let q : M →ₗ[R] (R ⧸ I) ⊗[R] M := TensorProduct.mk R (R ⧸ I) M 1
  have hqsmul (r : R) (x : M) :
      q (r • x) = Ideal.Quotient.mk I r • q x := by
    change q (r • x) = algebraMap R (R ⧸ I) r • q x
    rw [map_smul, IsScalarTower.algebraMap_smul]
  have hrel : ∑ i, Ideal.Quotient.mk I (f i : R) • q (x i) = 0 := by
    simpa only [map_sum, hqsmul, map_zero] using congrArg q hzero
  obtain ⟨k, a', y', hx, ha'⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  choose a ha using fun i j => Ideal.Quotient.mk_surjective (a' i j)
  choose y hy using fun j =>
    (IdealTensorRelation.exists_eq_one_tmul I (y' j)).imp fun _ h => h.symm
  let d : Fin n → M := fun i => x i - ∑ j, a i j • y j
  have hd (i : Fin n) : d i ∈ I • (⊤ : Submodule R M) := by
    have hqd : q (d i) = 0 := by
      simp only [d, map_sub, map_sum, hqsmul, ha]
      apply sub_eq_zero.mpr
      simpa only [q, TensorProduct.mk_apply, hy] using hx i
    have := congrArg (quotTensorEquivQuotSMul M I) hqd
    simpa only [q, TensorProduct.mk_apply, quotTensorEquivQuotSMul_mk_one_tmul, map_zero,
      Submodule.Quotient.mk_eq_zero] using this
  let b : Fin k → J := fun j => ∑ i, a i j • f i
  have hb (j : Fin k) : (b j : R) ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa [b, map_sum, map_mul, ha, mul_comm] using ha' j
  have hdecomp : (∑ i, f i ⊗ₜ[R] x i) =
      (∑ i, f i ⊗ₜ[R] d i) + ∑ j, b j ⊗ₜ[R] y j := by
    simp only [d, tmul_sub, tmul_sum, tmul_smul, Finset.sum_sub_distrib,
      b, sum_tmul, ← smul_tmul']
    rw [Finset.sum_comm]
    exact (sub_add_cancel _ _).symm
  rw [hdecomp]
  refine add_mem (Submodule.sum_mem _ fun i _ => tmul_mem_inclusion_range I J hIJ (f i) (hd i))
    (Submodule.sum_mem _ fun j _ => ?_)
  exact ⟨(⟨(b j : R), hb j⟩ : I) ⊗ₜ[R] y j, rfl⟩

/-- Flatness modulo I propagates tensor injectivity from I to every larger ideal. -/
theorem idealTensor_injective_of_quotient_flat (I J : Ideal R) (hIJ : I ≤ J)
    (hI : Function.Injective (I.subtype.rTensor M))
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M)] :
    Function.Injective (J.subtype.rTensor M) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨t, rfl⟩ := tensor_kernel_mem_inclusion_range I J hIJ z hz
  have hcomp : J.subtype ∘ₗ Submodule.inclusion hIJ = I.subtype := rfl
  have ht : I.subtype.rTensor M t = 0 := by
    rw [← hcomp, LinearMap.rTensor_comp_apply]
    exact hz
  rw [(injective_iff_map_eq_zero _).mp hI t ht, map_zero]

end TensorReduction

/-- Stacks Project, Lemma 10.99.10 (00ML), using the equational reduction
to the maximal-ideal local flatness criterion. -/
theorem idealLocalFlatnessCriterion : IdealLocalFlatnessCriterionStatement.{u, v, w} := by
  intro R S M _ _ _ _ _ _ _ _ _ _ _ _ I hI hfin hinj hflat
  let : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M) := hflat
  let : Module.Finite S M := hfin
  exact localFlatnessCriterion R S M
    (idealTensor_injective_of_quotient_flat I (IsLocalRing.maximalIdeal R)
      (IsLocalRing.le_maximalIdeal hI) hinj)

example : IdealLocalFlatnessCriterionStatement.{u, v, w} :=
  idealLocalFlatnessCriterion.{u, v, w}

end Langlands.Algebra
