import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Pi

/-! # Simultaneous trace separation of finite families of simple modules -/

noncomputable section

universe uA uM uI

namespace Langlands.FiniteSimpleTrace

variable {A : Type uA} [Ring A] [Algebra ℂ A]
variable {ι : Type uI} [Fintype ι] (M : ι → Type uM)
variable [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
variable [∀ i, Module A (M i)] [∀ i, IsScalarTower ℂ A (M i)]
variable [∀ i, FiniteDimensional ℂ (M i)] [∀ i, IsSimpleModule A (M i)]

/-- Density supplies one algebra element acting as the identity on a selected
simple module and as zero on all the inequivalent members of the family. -/
theorem exists_action_projection [DecidableEq ι]
    (hne : Pairwise (fun i k => ¬ Nonempty (M i ≃ₗ[A] M k))) (j : ι) :
    ∃ r : A, ∀ i, DistribSMul.toLinearMap ℂ (M i) r =
      if i = j then LinearMap.id else 0 := by
  classical
  have hcross (φ : Module.End A (∀ i, M i)) {i k : ι} (hik : i ≠ k)
      (v : M k) : φ (Pi.single k v) i = 0 := by
    let f : M k →ₗ[A] M i :=
      (LinearMap.proj i).comp (φ.comp (LinearMap.single A M k))
    have hf : f = 0 := f.bijective_or_eq_zero.resolve_left fun hf =>
      hne hik.symm ⟨LinearEquiv.ofBijective f hf⟩
    exact LinearMap.congr_fun hf v
  have hdiag (φ : Module.End A (∀ i, M i)) (i : ι) (x : ∀ i, M i) :
      φ x i = φ (Pi.single i (x i)) i := by
    calc
      φ x i = ∑ k, φ (Pi.single k (x k)) i := by
        conv_lhs => rw [← Finset.univ_sum_single x]
        rw [map_sum, Finset.sum_apply]
      _ = φ (Pi.single i (x i)) i := by
        apply Finset.sum_eq_single i
        · intro k _ hki
          exact hcross φ hki.symm (x k)
        · simp
  let p : Module.End (Module.End A (∀ i, M i)) (∀ i, M i) :=
    { toFun := fun x => Pi.single j (x j)
      map_add' := fun x y => by
        exact (LinearMap.single A M j).map_add (x j) (y j)
      map_smul' := fun φ x => by
        ext i
        change Pi.single j (φ x j) i = φ (Pi.single j (x j)) i
        by_cases hij : i = j
        · subst i
          simpa using hdiag φ j x
        · rw [Pi.single_eq_of_ne hij]
          exact (hcross φ hij (x j)).symm }
  let b := fun i => Module.finBasis ℂ (M i)
  let s : Finset (∀ i, M i) :=
    Finset.univ.biUnion fun i =>
      Finset.univ.image fun k => Pi.single i (b i k)
  obtain ⟨r, hr⟩ := jacobson_density p s
  refine ⟨r, fun i => (b i).ext fun k => ?_⟩
  have hk : Pi.single i (b i k) ∈ s :=
    Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i, Finset.mem_image_of_mem _ (Finset.mem_univ k)⟩
  have h := congrArg (fun x => x i) (hr _ hk)
  change Pi.single j (Pi.single i (b i k) j) i =
    r • (Pi.single i (b i k) i) at h
  by_cases hij : i = j
  · subst i
    simpa using h.symm
  · simpa [hij] using h.symm

/-- A complex linear relation among the traces of pairwise inequivalent
finite-dimensional simple modules has all coefficients zero. -/
theorem eq_zero_of_sum_trace_eq_zero
    (hne : Pairwise (fun i k => ¬ Nonempty (M i ≃ₗ[A] M k)))
    (c : ι → ℂ)
    (h : ∀ r : A, ∑ i, c i * LinearMap.trace ℂ (M i)
      (DistribSMul.toLinearMap ℂ (M i) r) = 0) :
    ∀ j, c j = 0 := by
  classical
  intro j
  obtain ⟨r, hr⟩ := exists_action_projection M hne j
  have hc : c j * (Module.finrank ℂ (M j) : ℂ) = 0 := by
    simpa [hr, apply_ite] using h r
  have : Nontrivial (M j) := IsSimpleModule.nontrivial A (M j)
  exact (mul_eq_zero.mp hc).resolve_right
    (Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℂ) (M := M j)).ne')

end Langlands.FiniteSimpleTrace
