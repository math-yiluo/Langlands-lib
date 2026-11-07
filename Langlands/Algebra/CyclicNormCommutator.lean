import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.Commutator.Basic

/-! A universe-general cyclic Hilbert 90 construction and its division-algebra commutator. -/

noncomputable section

namespace Langlands.CyclicNorm

universe uK uL uD

open scoped commutatorElement

variable {K : Type uK} [Field K] {L : Type uL} [Field L] [Algebra K L]

/-- The successive coefficient products in the cyclic Hilbert 90 sum. -/
def coefficient (σ : L ≃ₐ[K] L) (x : L) (n : ℕ) : L :=
  ∏ i ∈ Finset.range n, (σ ^ i) x

/-- The explicit cyclic Hilbert 90 weighted sum as a function of its last argument. -/
def weightedTrace (σ : L ≃ₐ[K] L) (x z : L) : L :=
  ∑ i ∈ Finset.range (orderOf σ), coefficient σ x i * (σ ^ i) z

theorem coefficient_shift (σ : L ≃ₐ[K] L) (x : L) (n : ℕ) :
    x * σ (coefficient σ x n) = coefficient σ x (n + 1) := by
  unfold coefficient
  rw [Finset.prod_range_succ', map_prod]
  simp only [pow_zero, AlgEquiv.one_apply]
  rw [mul_comm x]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [pow_succ', AlgEquiv.mul_apply]

theorem weightedTrace_relation (σ : L ≃ₐ[K] L) (x z : L)
    (hx : coefficient σ x (orderOf σ) = 1) :
    x * σ (weightedTrace σ x z) = weightedTrace σ x z := by
  calc
    _ = ∑ i ∈ Finset.range (orderOf σ),
        coefficient σ x (i + 1) * (σ ^ (i + 1)) z := by
      simp only [weightedTrace, map_sum, map_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← mul_assoc, coefficient_shift, pow_succ', AlgEquiv.mul_apply]
    _ = _ := by
      let f : ℕ → L := fun i => coefficient σ x i * (σ ^ i) z
      have h := Finset.sum_range_succ' f (orderOf σ)
      rw [Finset.sum_range_succ] at h
      have he : f (orderOf σ) = f 0 := by
        change coefficient σ x (orderOf σ) * (σ ^ orderOf σ) z =
          coefficient σ x 0 * (σ ^ 0) z
        rw [hx, pow_orderOf_eq_one, pow_zero]
        simp [coefficient]
      rw [he] at h
      exact (add_right_cancel h).symm

/-- The weighted sum is nonzero for some input, by independence of distinct automorphisms. -/
theorem exists_weightedTrace_ne_zero (σ : L ≃ₐ[K] L) (x : L)
    (hσ : IsOfFinOrder σ) : ∃ z, weightedTrace σ x z ≠ 0 := by
  classical
  have hli : LinearIndependent L
      (fun i : Fin (orderOf σ) => (fun z : L => (σ ^ (i : ℕ)) z)) := by
    apply (linearIndependent_monoidHom L L).comp
      (fun i : Fin (orderOf σ) => (σ ^ (i : ℕ)).toMonoidHom)
    intro i j hij
    apply Fin.ext
    apply (pow_injOn_Iio_orderOf (x := σ)) i.isLt j.isLt
    apply AlgEquiv.ext
    intro z
    exact congrArg (fun f : L →* L => f z) hij
  by_contra h
  have hz (z : L) : weightedTrace σ x z = 0 := by
    by_contra hn
    exact h ⟨z, hn⟩
  have hsum : (∑ i : Fin (orderOf σ),
      coefficient σ x i • (fun z : L => (σ ^ (i : ℕ)) z)) = 0 := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    change (∑ i : Fin (orderOf σ),
      (fun n : ℕ => coefficient σ x n * (σ ^ n) z) i) = 0
    exact (Fin.sum_univ_eq_sum_range
      (fun n : ℕ => coefficient σ x n * (σ ^ n) z) (orderOf σ)).trans (hz z)
  have hc := (Fintype.linearIndependent_iff.mp hli) _ hsum ⟨0, hσ.orderOf_pos⟩
  simp [coefficient] at hc

section Galois

variable [FiniteDimensional K L] [IsGalois K L]

theorem coefficient_order_eq_norm (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) (x : L) :
    coefficient σ x (orderOf σ) = algebraMap K L (Algebra.norm K x) := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms, coefficient,
    ← IsCyclic.image_range_orderOf hσ]
  symm
  apply Finset.prod_image
  intro i hi j hj hij
  exact (pow_injOn_Iio_orderOf (x := σ))
    (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij

/-- Cyclic Hilbert 90 for fields in arbitrary independent universes. -/
theorem exists_div_of_norm_eq_one (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) {x : L}
    (hx : Algebra.norm K x = 1) : ∃ y : Lˣ, (y : L) / σ (y : L) = x := by
  have hc : coefficient σ x (orderOf σ) = 1 := by
    rw [coefficient_order_eq_norm σ hσ, hx, map_one]
  obtain ⟨z, hz⟩ := exists_weightedTrace_ne_zero σ x (isOfFinOrder_of_finite σ)
  refine ⟨Units.mk0 (weightedTrace σ x z) hz, ?_⟩
  change weightedTrace σ x z / σ (weightedTrace σ x z) = x
  have hne : σ (weightedTrace σ x z) ≠ 0 := by
    intro h
    apply hz
    apply σ.injective
    simpa using h
  exact (div_eq_iff hne).mpr (weightedTrace_relation σ x z hc).symm

variable {D : Type uD} [Ring D] [Algebra K D]

/-- A norm-one coefficient gives a single commutator whenever a unit implements the cyclic generator. -/
theorem exists_commutator_of_norm_eq_one (ι : L →ₐ[K] D) (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) (u : Dˣ)
    (hu : ∀ a : L, (u : D) * ι a * ((u⁻¹ : Dˣ) : D) = ι (σ a))
    (x : Lˣ) (hx : Algebra.norm K (x : L) = 1) :
    ∃ v : Dˣ, Units.map ι.toMonoidHom x = ⁅v, u⁆ := by
  obtain ⟨y, hy⟩ := exists_div_of_norm_eq_one σ hσ hx
  let v : Dˣ := Units.map ι.toMonoidHom y
  have hy' : y * (Units.map σ.toMonoidHom y)⁻¹ = x := by
    apply Units.ext
    simpa [div_eq_mul_inv] using hy
  have hconj : u * v * u⁻¹ =
      Units.map ι.toMonoidHom (Units.map σ.toMonoidHom y) := by
    apply Units.ext
    exact hu (y : L)
  refine ⟨v, ?_⟩
  calc
    Units.map ι.toMonoidHom x =
        Units.map ι.toMonoidHom (y * (Units.map σ.toMonoidHom y)⁻¹) :=
      congrArg (Units.map ι.toMonoidHom) hy'.symm
    _ = v * (u * v * u⁻¹)⁻¹ := by rw [map_mul, map_inv, ← hconj]
    _ = ⁅v, u⁆ := by
      simp [commutatorElement_def, mul_inv_rev, mul_assoc]

/-- The image of each such norm-one unit belongs to the actual coefficient-unit commutator subgroup. -/
theorem map_mem_commutator_of_norm_eq_one (ι : L →ₐ[K] D) (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) (u : Dˣ)
    (hu : ∀ a : L, (u : D) * ι a * ((u⁻¹ : Dˣ) : D) = ι (σ a))
    (x : Lˣ) (hx : Algebra.norm K (x : L) = 1) :
    Units.map ι.toMonoidHom x ∈ commutator Dˣ := by
  obtain ⟨v, hv⟩ := exists_commutator_of_norm_eq_one ι σ hσ u hu x hx
  rw [hv]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top v) (Subgroup.mem_top u)

end Galois

end Langlands.CyclicNorm
