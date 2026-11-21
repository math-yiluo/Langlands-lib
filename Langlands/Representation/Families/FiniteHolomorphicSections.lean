import Mathlib.Algebra.FreeAlgebra
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Finite families of sections with entire scalar coefficients -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Curves made of finite sums of entire scalar functions times constant sections. -/
def finiteHolomorphicSections (E V : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [AddCommGroup V] [Module ℂ V] : Submodule ℂ (E → V) :=
  Submodule.span ℂ (Set.range fun x : {a : E → ℂ // Differentiable ℂ a} × V =>
    fun t => x.1.val t • x.2)

namespace FiniteHolomorphicSections

/-- The span has the stated finite expansion in entire scalar functions. -/
theorem mem_iff {f : E → V} : f ∈ finiteHolomorphicSections E V ↔
    ∃ (m : ℕ) (a : Fin m → E → ℂ) (v : Fin m → V),
      (∀ j, Differentiable ℂ (a j)) ∧ ∀ t, f t = ∑ j, a j t • v j := by
  classical
  constructor
  · intro hf
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hf
    let e := (Fintype.equivFin ↥c.support).symm
    let a (i : Fin (Fintype.card ↥c.support)) (t : E) := c (e i).val * (e i).val.1.val t
    let v (i : Fin (Fintype.card ↥c.support)) := (e i).val.2
    refine ⟨_, a, v, fun i => (differentiable_const _).mul (e i).val.1.property, fun t => ?_⟩
    calc
      f t = ∑ j ∈ c.support, (c j * j.1.val t) • j.2 := by
        rw [← hc, Finsupp.sum, Finset.sum_apply]
        simp only [Pi.smul_apply, mul_smul]
      _ = ∑ j : ↥c.support, (c j.val * j.val.1.val t) • j.val.2 :=
        (Finset.sum_coe_sort _ _).symm
      _ = _ := (Equiv.sum_comp e (fun j : ↥c.support => (c j.val * j.val.1.val t) • j.val.2)).symm
  · rintro ⟨m, a, v, ha, hv⟩
    have heq : f = ∑ j, fun t => a j t • v j := by
      funext t
      rw [Finset.sum_apply, hv]
    rw [heq]
    exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨(⟨a j, ha j⟩, v j), rfl⟩

/-- One entire scalar multiple of a constant section belongs to the submodule. -/
theorem smul_const_mem (a : E → ℂ) (ha : Differentiable ℂ a) (v : V) :
    (fun t => a t • v) ∈ finiteHolomorphicSections E V :=
  Submodule.subset_span ⟨(⟨a, ha⟩, v), rfl⟩

theorem const_mem (v : V) : (fun _ : E => v) ∈ finiteHolomorphicSections E V := by
  simpa only [one_smul] using smul_const_mem (fun _ : E => (1 : ℂ)) (differentiable_const _) v

theorem smul_mem (a : E → ℂ) (ha : Differentiable ℂ a) {f : E → V}
    (hf : f ∈ finiteHolomorphicSections E V) :
    (fun t => a t • f t) ∈ finiteHolomorphicSections E V := by
  obtain ⟨m, c, v, hc, heq⟩ := mem_iff.mp hf
  refine mem_iff.mpr ⟨m, fun i t => a t * c i t, v, fun i => ha.mul (hc i), fun t => ?_⟩
  rw [heq t, Finset.smul_sum]
  simp only [mul_smul]

theorem map_mem (l : V →ₗ[ℂ] W) {f : E → V} (hf : f ∈ finiteHolomorphicSections E V) :
    (fun t => l (f t)) ∈ finiteHolomorphicSections E W := by
  obtain ⟨m, a, v, ha, heq⟩ := mem_iff.mp hf
  refine mem_iff.mpr ⟨m, a, fun i => l (v i), ha, fun t => ?_⟩
  simp only [heq t, map_sum, map_smul]

/-- An injective scalar realization reflects finite holomorphic expansions. -/
theorem mem_of_injective (l : V →ₗ[ℂ] W) (hl : Function.Injective l) {f : E → V}
    (hf : (fun t => l (f t)) ∈ finiteHolomorphicSections E W) : f ∈ finiteHolomorphicSections E V := by
  simpa only [LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hl)] using
    map_mem l.leftInverse hf

/-- The values of one such curve lie in a common finite-dimensional subspace. -/
theorem exists_finiteDimensional_range {f : E → V} (hf : f ∈ finiteHolomorphicSections E V) :
    ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ ∀ t, f t ∈ S := by
  obtain ⟨m, a, v, _ha, heq⟩ := mem_iff.mp hf
  refine ⟨Submodule.span ℂ (Set.range v), FiniteDimensional.span_of_finite _ (Set.finite_range v), ?_⟩
  intro t
  rw [heq t]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- Each linear scalar test on such a family is entire. -/
theorem differentiable_apply {f : E → V} (hf : f ∈ finiteHolomorphicSections E V)
    (l : V →ₗ[ℂ] ℂ) : Differentiable ℂ (fun t => l (f t)) := by
  obtain ⟨m, a, v, ha, heq⟩ := mem_iff.mp hf
  simp only [heq, map_sum, map_smul, smul_eq_mul]
  exact Differentiable.fun_sum fun j _ => (ha j).mul_const _

/-- A varying linear operator preserving finite holomorphic families on
constant sections also preserves them on varying sections. -/
theorem apply_mem (T : E → V →ₗ[ℂ] W)
    (hT : ∀ v, (fun t => T t v) ∈ finiteHolomorphicSections E W)
    {f : E → V} (hf : f ∈ finiteHolomorphicSections E V) :
    (fun t => T t (f t)) ∈ finiteHolomorphicSections E W := by
  obtain ⟨m, a, v, ha, heq⟩ := mem_iff.mp hf
  have hsum : (fun t => T t (f t)) = ∑ j, fun t => a j t • T t (v j) := by
    funext t
    simp only [heq, map_sum, map_smul, Finset.sum_apply]
  rw [hsum]
  exact Submodule.sum_mem _ fun j _ => smul_mem (a j) (ha j) (hT (v j))

/-- The property for the individual generators passes to every free operator. -/
theorem freeAlgebra_apply_mem {I : Type*}
    (T : E → FreeAlgebra ℂ I →ₐ[ℂ] Module.End ℂ V)
    (hT : ∀ i v, (fun t => T t (FreeAlgebra.ι ℂ i) v) ∈ finiteHolomorphicSections E V)
    (a : FreeAlgebra ℂ I) (v : V) : (fun t => T t a v) ∈ finiteHolomorphicSections E V := by
  induction a using FreeAlgebra.induction generalizing v with
  | grade0 c => simpa only [AlgHom.commutes, Module.algebraMap_end_apply] using const_mem (E := E) (c • v)
  | grade1 i => exact hT i v
  | add a b ha hb =>
    have heq : (fun t => T t (a + b) v) = (fun t => T t a v) + (fun t => T t b v) := by
      funext t
      simp only [map_add, LinearMap.add_apply, Pi.add_apply]
    rw [heq]
    exact (finiteHolomorphicSections E V).add_mem (ha v) (hb v)
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_apply]
    exact apply_mem (fun t => T t a) ha (hb v)

/-- A vector of the free module on constant sections gives a finite holomorphic section family. -/
theorem freeAlgebra_finsuppSum_mem {I J : Type*}
    (T : E → FreeAlgebra ℂ I →ₐ[ℂ] Module.End ℂ V)
    (hT : ∀ i v, (fun t => T t (FreeAlgebra.ι ℂ i) v) ∈ finiteHolomorphicSections E V)
    (v : J → V) (w : J →₀ FreeAlgebra ℂ I) :
    (fun t => w.sum fun j a => T t a (v j)) ∈ finiteHolomorphicSections E V := by
  classical
  have heq : (fun t => w.sum fun j a => T t a (v j)) =
      ∑ j ∈ w.support, fun t => T t (w j) (v j) := by
    funext t
    rw [Finsupp.sum, Finset.sum_apply]
  rw [heq]
  exact Submodule.sum_mem _ fun j _ => freeAlgebra_apply_mem T hT (w j) (v j)

end FiniteHolomorphicSections

end Langlands
