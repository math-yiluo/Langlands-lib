import Langlands.GroupScheme.Unipotent.OneDimensional.Cocycle
import Langlands.AnthropicFLT.Theorems.Thm_Algebra_exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType
import Langlands.AnthropicFLT.Theorems.Thm_Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent

/-! # Consequences of Krull dimension at most one for a finitely generated domain -/

noncomputable section

universe u

open Polynomial

namespace Langlands.GroupScheme.Unipotent.OneDimensional

variable {k B : Type u} [Field k] [CommRing B] [IsDomain B] [Algebra k B]
  [Algebra.FiniteType k B]

/-- In a finitely generated domain of dimension at most one, the quotient by a nonzero
element is finite-dimensional. -/
theorem finite_quotient_span_singleton (hdim : ringKrullDim B ≤ 1) {z : B} (hz : z ≠ 0) :
    Module.Finite k (B ⧸ Ideal.span {z}) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have : Ring.KrullDimLE 1 B := by
    rw [Ring.KrullDimLE, Order.krullDimLE_iff]
    exact_mod_cast hdim
  have : IsArtinianRing (B ⧸ Ideal.span {z}) := by
    rw [isArtinianRing_iff_krullDimLE_zero, Ring.KrullDimLE, Order.krullDimLE_iff,
      ← ENat.WithBot.add_le_add_one_right_iff, Nat.cast_zero, zero_add]
    exact (ringKrullDim_quotient_succ_le_of_nonZeroDivisor
      (mem_nonZeroDivisors_of_ne_zero hz)).trans Order.KrullDimLE.krullDim_le
  exact Module.finite_of_isArtinianRing k _

/-- A finitely generated domain of dimension at most one has transcendence degree at most
one. -/
theorem trdeg_le_one (hdim : ringKrullDim B ≤ 1) : Algebra.trdeg k B ≤ 1 := by
  have : FaithfulSMul k B :=
    (faithfulSMul_iff_algebraMap_injective k B).mpr (algebraMap k B).injective
  obtain ⟨r, hr, d, z, hz, hint⟩ :=
    Algebra.exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType
      (R := k) (C := B)
  -- Noether normalization bounds the number of algebraically independent elements.
  have hQ : (⊥ : Ideal B) ∈ ((⊥ : Ideal k).map (algebraMap k B)).minimalPrimes := by
    rw [Ideal.map_bot, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
  have hd := Ideal.natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent
    k z hz r hr hint ⊥ (by simpa using hr) ⊥ hQ
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot B)] at hd
  have hd1 : d ≤ 1 := by exact_mod_cast hd.trans hdim
  -- `B` is algebraic over the polynomial subalgebra.
  have : Algebra.IsIntegral (Algebra.adjoin k (Set.range z)) B := by
    refine ⟨fun c => ?_⟩
    obtain ⟨n, hn⟩ := hint c
    have h := hn.smul (r ^ n)⁻¹
    rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero n hr), one_smul] at h
  have : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range z)) B :=
    Algebra.IsIntegral.isAlgebraic
  calc Algebra.trdeg k B ≤ Cardinal.mk (Set.range z) :=
        Algebra.IsAlgebraic.trdeg_le_cardinalMk k (Set.range z)
    _ ≤ d := by simpa using Cardinal.mk_range_le_lift (f := z)
    _ ≤ 1 := by exact_mod_cast hd1

omit [IsDomain B] [Algebra.FiniteType k B] in
/-- Any two elements of an algebra of transcendence degree at most one satisfy a nonzero
polynomial relation. -/
theorem exists_ev2_eq_zero (htr : Algebra.trdeg k B ≤ 1) (y t : B) :
    ∃ c : k[X][X], c ≠ 0 ∧ ev2 y t c = 0 := by
  by_contra h
  push Not at h
  have hinj : Function.Injective (ev2 y t : k[X][X] →ₐ[k] B) :=
    (injective_iff_map_eq_zero _).mpr fun c hc => by
      by_contra hc0
      exact h c hc0 hc
  have h2 := trdeg_le_of_injective (ev2 y t : k[X][X] →ₐ[k] B) hinj
  have h3 := trdeg_add_le (R := k) (S := k[X]) (A := k[X][X])
  rw [Polynomial.trdeg_of_isDomain, Polynomial.trdeg_of_isDomain] at h3
  have h4 : ((2 : ℕ) : Cardinal) ≤ ((1 : ℕ) : Cardinal) := by
    rw [Nat.cast_ofNat, Nat.cast_one, ← one_add_one_eq_two]
    exact h3.trans (h2.trans htr)
  exact absurd (Nat.cast_le.mp h4) (by norm_num)

end Langlands.GroupScheme.Unipotent.OneDimensional
