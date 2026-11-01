import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Algebra.Module.SpanRankOperations

/-! # Minimal finite free covers over a local ring -/

universe u v

namespace Langlands.CommutativeAlgebra

open Module TensorProduct

variable (R : Type u) [CommRing R] [IsLocalRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- A finite free cover whose kernel is contained in the maximal-ideal multiple
of the source. -/
structure MinimalFiniteFreeCover where
  rank : ℕ
  map : (Fin rank →₀ R) →ₗ[R] M
  surjective : Function.Surjective map
  minimal : LinearMap.ker map ≤
    IsLocalRing.maximalIdeal R • (⊤ : Submodule R (Fin rank →₀ R))

variable {R M}

lemma ker_le_maximalIdeal_smul_of_residue_injective
    {F : Type*} [AddCommGroup F] [Module R F] (f : F →ₗ[R] M)
    (hf : Function.Injective (f.lTensor (IsLocalRing.ResidueField R))) :
    LinearMap.ker f ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R F) := by
  intro x hx
  rw [← LinearMap.ker_tensorProductMk]
  change (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x = 0
  apply hf
  simp only [LinearMap.lTensor_tmul, LinearMap.mem_ker.mp hx, tmul_zero, map_zero]

variable (R M)

/-- Lift a residue-field basis and apply Nakayama to obtain a minimal finite free
cover. No Noetherian hypothesis is needed for its existence. -/
theorem nonempty_minimalFiniteFreeCover [Module.Finite R M] :
    Nonempty (MinimalFiniteFreeCover R M) := by
  classical
  let k := IsLocalRing.ResidueField R
  let n := Module.finrank k (k ⊗[R] M)
  let b : Basis (Fin n) k (k ⊗[R] M) := Module.finBasis k (k ⊗[R] M)
  obtain ⟨v, hv⟩ := (TensorProduct.mk_surjective R M k
    Ideal.Quotient.mk_surjective).comp_left b
  let f := Finsupp.linearCombination R v
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact IsLocalRing.span_eq_top_of_tmul_eq_basis v b (congr_fun hv)
  have hinj : Function.Injective (f.baseChange k) := by
    apply (OrzechProperty.bijective_of_surjective_of_finrank_le
      (f.baseChange k) (f.lTensor_surjective k hsurj) ?_).injective
    simp only [Module.finrank_tensorProduct, Module.finrank_self,
      Module.finrank_finsupp_self, Fintype.card_fin, one_mul]
    exact le_rfl
  refine ⟨⟨n, f, hsurj, ?_⟩⟩
  apply ker_le_maximalIdeal_smul_of_residue_injective
  exact hinj

/-- A chosen minimal finite free cover of a finite module. -/
noncomputable def minimalFiniteFreeCover [Module.Finite R M] :
    MinimalFiniteFreeCover R M :=
  Classical.choice (nonempty_minimalFiniteFreeCover R M)

end Langlands.CommutativeAlgebra
