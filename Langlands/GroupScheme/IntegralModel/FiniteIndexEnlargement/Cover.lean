import Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement.PointTranslation
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! # Covering a Hopf algebra by translates of an element with unit counit

Let `R` be a local ring and `ϖ ∈ R`. Suppose a family of `R`-linear forms `σ z` on an
`R`-module `C` detects divisibility by `ϖ`: if all `σ z c` lie in the maximal ideal then `c` is
divisible by `ϖ`. Then an element `t` of `M ⊗[R] C`, for an `R`-module `M` killed by `ϖ`, is zero
as soon as all its contractions `(id ⊗ σ z) t ∈ M` vanish.

For a commutative Hopf algebra `C` over `R`, a family of integral points `τ z` detecting
divisibility by `ϖ`, and an element `e` whose counit is a unit, this shows that `ϖ` and the
translates of `e` by the points `τ z` generate the unit ideal: modulo the ideal they generate,
the class of `Δ e` is killed by every `τ z`, hence vanishes, and multiplying out with the
antipode gives the unit `ε e`. -/

noncomputable section

open TensorProduct

namespace Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement

section Linear

variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {C : Type*} [AddCommGroup C] [Module R C] {Z : Type*}

omit [IsLocalRing R] in
theorem rid_lTensor_sum {n : ℕ} (σ : C →ₗ[R] R) (m : Fin n → M) (c : Fin n → C) :
    TensorProduct.rid R M (LinearMap.lTensor M σ (∑ i, m i ⊗ₜ[R] c i)) = ∑ i, σ (c i) • m i := by
  simp [map_sum]

/-- Elements of `M ⊗[R] C` killed by enough linear forms on `C` vanish, when `ϖ` kills `M` and
the forms detect divisibility by `ϖ`. -/
theorem eq_zero_of_forall_rid_lTensor {ϖ : R} (hM : ∀ m : M, ϖ • m = 0) (σ : Z → C →ₗ[R] R)
    (hσ : ∀ c : C, (∀ z, σ z c ∈ IsLocalRing.maximalIdeal R) → ∃ c', c = ϖ • c')
    (t : M ⊗[R] C) (ht : ∀ z, TensorProduct.rid R M (LinearMap.lTensor M (σ z) t) = 0) :
    t = 0 := by
  obtain ⟨n, m, c, rfl⟩ := TensorProduct.exists_sum_tmul_eq t
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hall : ∀ j z, σ z (c j) ∈ IsLocalRing.maximalIdeal R
    · apply Finset.sum_eq_zero
      intro j _
      obtain ⟨c', hc'⟩ := hσ (c j) (hall j)
      rw [hc', TensorProduct.tmul_smul, TensorProduct.smul_tmul', hM, TensorProduct.zero_tmul]
    · push Not at hall
      obtain ⟨j, z, hjz⟩ := hall
      obtain ⟨u, hu⟩ := IsLocalRing.notMem_maximalIdeal.mp hjz
      have hrel := ht z
      rw [rid_lTensor_sum, Fin.sum_univ_succAbove _ j] at hrel
      -- eliminate the `j`-th term
      have hsum : ∑ i, m i ⊗ₜ[R] c i =
          ∑ i : Fin n, m (j.succAbove i) ⊗ₜ[R]
            (c (j.succAbove i) - ((↑u⁻¹ : R) * σ z (c (j.succAbove i))) • c j) := by
        have hmj : m j = -((↑u⁻¹ : R) • ∑ i : Fin n, σ z (c (j.succAbove i)) • m (j.succAbove i)) := by
          have h1 : (u : R) • m j = -∑ i : Fin n, σ z (c (j.succAbove i)) • m (j.succAbove i) := by
            rw [hu]
            exact eq_neg_of_add_eq_zero_left hrel
          rw [← smul_neg, ← h1, smul_smul, Units.inv_mul, one_smul]
        rw [Fin.sum_univ_succAbove _ j]
        simp only [TensorProduct.tmul_sub, Finset.sum_sub_distrib]
        rw [hmj, TensorProduct.neg_tmul, Finset.smul_sum, TensorProduct.sum_tmul]
        simp only [smul_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        abel
      rw [hsum]
      apply ih
      rw [← hsum]
      exact ht

end Linear

section Hopf

variable {R : Type*} [CommRing R] [IsLocalRing R] {C : Type*} [CommRing C] [HopfAlgebra R C]
  {Z : Type*}

omit [IsLocalRing R] in
theorem rid_lTensor_rTensor_mkₐ (I : Ideal C) (f : C →ₗ[R] R) (w : C ⊗[R] C) :
    TensorProduct.rid R (C ⧸ I) (LinearMap.lTensor (C ⧸ I) f
        (LinearMap.rTensor C (Ideal.Quotient.mkₐ R I).toLinearMap w)) =
      Ideal.Quotient.mk I (TensorProduct.rid R C (LinearMap.lTensor C f w)) := by
  induction w using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
      AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, map_add, map_add]

omit [IsLocalRing R] in
theorem mul'_map_rTensor_mkₐ (I : Ideal C) (w : C ⊗[R] C) :
    LinearMap.mul' R (C ⧸ I) (TensorProduct.map LinearMap.id
        ((Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ HopfAlgebra.antipode R)
        (LinearMap.rTensor C (Ideal.Quotient.mkₐ R I).toLinearMap w)) =
      Ideal.Quotient.mk I (LinearMap.mul' R C ((HopfAlgebra.antipode R).lTensor C w)) := by
  induction w using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, map_add, map_add]

/-- **Covering lemma.** If integral points `τ z` of a commutative Hopf algebra detect
divisibility by `ϖ`, then for every `e` with unit counit, `ϖ` and the translates of `e` by the
points `τ z` generate the unit ideal. -/
theorem span_insert_pointTrans_eq_top {ϖ : R} (τ : Z → C →ₐ[R] R)
    (hτ : ∀ c : C, (∀ z, τ z c ∈ IsLocalRing.maximalIdeal R) → ∃ c', c = ϖ • c')
    {e : C} (he : IsUnit (Coalgebra.counit (R := R) e)) :
    Ideal.span (insert (algebraMap R C ϖ) (Set.range fun z => pointTrans (τ z) e)) = ⊤ := by
  set I := Ideal.span (insert (algebraMap R C ϖ) (Set.range fun z => pointTrans (τ z) e))
  set q := Ideal.Quotient.mkₐ R I
  have hϖI : algebraMap R C ϖ ∈ I := Ideal.subset_span (Set.mem_insert _ _)
  have hM : ∀ m : C ⧸ I, ϖ • m = 0 := by
    intro m
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
    rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact I.mul_mem_right _ hϖI
  have ht : LinearMap.rTensor C q.toLinearMap (Coalgebra.comul (R := R) e) = 0 := by
    apply eq_zero_of_forall_rid_lTensor hM (fun z => (τ z).toLinearMap) hτ
    intro z
    rw [rid_lTensor_rTensor_mkₐ, ← pointTrans_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨z, rfl⟩)
  have hε := mul'_map_rTensor_mkₐ (R := R) I (Coalgebra.comul (R := R) e)
  rw [ht, map_zero, map_zero, HopfAlgebra.mul_antipode_lTensor_comul_apply, eq_comm,
    Ideal.Quotient.eq_zero_iff_mem] at hε
  exact Ideal.eq_top_of_isUnit_mem _ hε (he.map (algebraMap R C))

end Hopf

end Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement
