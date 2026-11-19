import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Complex.Basic

/-! # Riesz theory: identity plus a compact operator is Fredholm -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic.RieszFredholm

open ContinuousLinearMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The kernel of `1 + K` is finite-dimensional when `K` is compact. -/
theorem finiteDimensional_ker_id_add {K : X →L[ℂ] X} (hK : IsCompactOperator K) :
    FiniteDimensional ℂ (ContinuousLinearMap.id ℂ X + K).ker := by
  set V := (ContinuousLinearMap.id ℂ X + K).ker with hV
  have hmem : ∀ v ∈ V, K v = -v := by
    intro v hv
    have : v + K v = 0 := by simpa [hV] using hv
    exact eq_neg_of_add_eq_zero_right this
  have hmaps : ∀ v ∈ V, (K : X →ₗ[ℂ] X) v ∈ V := by
    intro v hv
    have := hmem v hv
    simp only [ContinuousLinearMap.coe_coe, this]
    exact V.neg_mem hv
  have hclosed : IsClosed (V : Set X) := (ContinuousLinearMap.id ℂ X + K).isClosed_ker
  have hc : IsCompactOperator ((K : X →ₗ[ℂ] X).restrict hmaps) := hK.restrict hmaps hclosed
  have hc' : IsCompactOperator (_root_.id : V → V) := by
    have := hc.neg
    convert this using 1
    funext v
    ext
    simp [LinearMap.restrict_apply, hmem v v.2]
  exact FiniteDimensional.of_isCompactOperator_id hc'

/-- The rank-one operator `x ↦ f x • y` has finite range. -/
theorem hasFiniteRange_smulRight (f : StrongDual ℂ X) (y : X) :
    (f.smulRight y : X →L[ℂ] X).toLinearMap.HasFiniteRange := by
  have h : (f.smulRight y : X →L[ℂ] X).toLinearMap =
      ((ContinuousLinearMap.id ℂ ℂ).smulRight y : ℂ →L[ℂ] X).toLinearMap ∘ₗ f.toLinearMap := by
    ext x; simp
  rw [h]
  exact LinearMap.HasFiniteRange.comp_left LinearMap.HasFiniteRange.of_isNoetherian_rng _

/-- The rank-one operator `x ↦ f x • y` is compact. -/
theorem isCompactOperator_smulRight (f : StrongDual ℂ X) (y : X) :
    IsCompactOperator (f.smulRight y : X →L[ℂ] X) := by
  have h : (f.smulRight y : X →L[ℂ] X) =
      ((ContinuousLinearMap.id ℂ ℂ).smulRight y : ℂ →L[ℂ] X) ∘L f := by
    ext x; simp
  rw [h]
  exact (isCompactOperator_of_locallyCompactSpace_dom (f : X →L[ℂ] ℂ)).clm_comp
    ((ContinuousLinearMap.id ℂ ℂ).smulRight y)

variable [CompleteSpace X]

/-- **Riesz theory**: for a compact operator `K` on a complex Banach space, `1 + K` is a
Fredholm operator. -/
theorem isFredholm_id_add {K : X →L[ℂ] X} (hK : IsCompactOperator K) :
    IsFredholm (ContinuousLinearMap.id ℂ X + K) := by
  suffices h : ∀ n : ℕ, ∀ K : X →L[ℂ] X, IsCompactOperator K →
      Module.finrank ℂ (ContinuousLinearMap.id ℂ X + K).ker = n →
      IsFredholm (ContinuousLinearMap.id ℂ X + K) from h _ K hK rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K hK hn
  have hfin := finiteDimensional_ker_id_add hK
  by_cases hsurj : Function.Surjective (ContinuousLinearMap.id ℂ X + K)
  · refine (Function.Surjective.isFredholm_iff _ hsurj).2 ⟨?_, ?_, hfin⟩
    · exact (ContinuousLinearMap.isOpenMap _ hsurj).isQuotientMap
        (ContinuousLinearMap.continuous _) hsurj
    · exact Submodule.ClosedComplemented.of_finiteDimensional _
  · obtain ⟨y, hy⟩ : ∃ y, ∀ a, (ContinuousLinearMap.id ℂ X + K) a ≠ y := by
      by_contra! h
      exact hsurj h
    have hker : (ContinuousLinearMap.id ℂ X + K).ker ≠ ⊥ := by
      intro hbot
      have hev : ¬ Module.End.HasEigenvalue (K : Module.End ℂ X) (-1) := by
        intro hev
        obtain ⟨x, hx⟩ := hev.exists_hasEigenvector
        rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
        apply hx.2
        have hxk : x ∈ (ContinuousLinearMap.id ℂ X + K).ker := by
          rw [LinearMap.mem_ker]
          have h1 := hx.1
          simp only [ContinuousLinearMap.coe_coe] at h1
          simp [h1]
        rw [hbot] at hxk
        simpa using hxk
      have hres := (hK.hasEigenvalue_or_mem_resolventSet (μ := (-1 : ℂ)) (by norm_num)).resolve_left
        hev
      rw [spectrum.mem_resolventSet_iff] at hres
      have hunit : IsUnit (ContinuousLinearMap.id ℂ X + K) := by
        have h1 : ContinuousLinearMap.id ℂ X + K = -(algebraMap ℂ (X →L[ℂ] X) (-1) - K) := by
          ext x; simp [add_comm]
        rw [h1]; exact hres.neg
      exact hsurj (ContinuousLinearMap.isUnit_iff_bijective.1 hunit).2
    obtain ⟨x, hxker, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    obtain ⟨f, -, hfx⟩ := exists_dual_vector ℂ x (norm_ne_zero_iff.2 hx0)
    have hfx0 : f x ≠ 0 := by
      rw [hfx]; simpa using hx0
    set K' := K + f.smulRight y with hK'
    have hK'c : IsCompactOperator K' := hK.add (isCompactOperator_smulRight f y)
    have hker' : (ContinuousLinearMap.id ℂ X + K').ker < (ContinuousLinearMap.id ℂ X + K).ker := by
      refine lt_of_le_of_ne ?_ ?_
      · intro v hv
        rw [LinearMap.mem_ker] at hv ⊢
        have h1 : (ContinuousLinearMap.id ℂ X + K) v = -(f v • y) := by
          simp only [hK', ContinuousLinearMap.coe_coe, add_apply,
            ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply] at hv ⊢
          rw [← add_assoc] at hv
          exact eq_neg_of_add_eq_zero_left hv
        by_cases hfv : f v = 0
        · simpa [hfv] using h1
        · exfalso
          apply hy (-(f v)⁻¹ • v)
          simp only [map_smul] at h1 ⊢
          rw [h1, smul_neg, neg_smul, neg_neg, smul_smul, inv_mul_cancel₀ hfv, one_smul]
      · intro heq
        have hx' : x ∈ (ContinuousLinearMap.id ℂ X + K').ker := heq ▸ hxker
        rw [LinearMap.mem_ker] at hx' hxker
        simp only [hK', ContinuousLinearMap.coe_coe, add_apply,
          ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply] at hx' hxker
        rw [← add_assoc, hxker, zero_add, smul_eq_zero] at hx'
        rcases hx' with h | h
        · exact hfx0 h
        · exact hy 0 (by simp [h])
    have hlt : Module.finrank ℂ (ContinuousLinearMap.id ℂ X + K').ker < n :=
      hn ▸ Submodule.finrank_lt_finrank_of_lt hker'
    have hF := ih _ hlt K' hK'c rfl
    have h1 : ContinuousLinearMap.id ℂ X + K =
        (ContinuousLinearMap.id ℂ X + K') + (-(f.smulRight y)) := by
      rw [hK']; abel
    rw [h1]
    refine hF.add_hasFiniteRange ?_
    simpa using (hasFiniteRange_smulRight f y).neg

open scoped LinearMap.FiniteRangeSetoid in
/-- If `D ∘ A - 1` is compact, then `A` has a left inverse modulo a finite-rank operator:
there are `G` and `F` with `G ∘ A = 1 - F` and `F` of finite-dimensional range. -/
theorem exists_leftInverse_mod_finiteRank {C : Type*} [NormedAddCommGroup C] [NormedSpace ℂ C]
    (A : X →L[ℂ] C) (D : C →L[ℂ] X)
    (hK : IsCompactOperator (D ∘L A - ContinuousLinearMap.id ℂ X)) :
    ∃ (G : C →L[ℂ] X) (F : X →L[ℂ] X), FiniteDimensional ℂ (LinearMap.range (F : X →ₗ[ℂ] X)) ∧
      G ∘L A = ContinuousLinearMap.id ℂ X - F := by
  have h := isFredholm_id_add hK
  rw [add_sub_cancel] at h
  obtain ⟨Q, hQ⟩ := h.exists_isQuasiInverse
  refine ⟨Q ∘L D, ContinuousLinearMap.id ℂ X - Q ∘L D ∘L A, ?_, by rw [sub_sub_cancel]; rfl⟩
  have h1 := hQ.1
  rw [LinearMap.IsLeftQuasiInverse, LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange] at h1
  have h2 := h1.neg
  rw [neg_sub] at h2
  exact Module.Finite.iff_fg.mpr h2

end Langlands.Analysis.Meromorphic.RieszFredholm
