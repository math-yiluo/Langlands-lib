import Langlands.Algebra.UnitaryInvolutionStatements
import Langlands.Algebra.LocalUnitaryQuaternion
import Langlands.Algebra.LocalQuadraticDichotomy
import Langlands.LocalField.FiniteExtension

/-!
# Division algebras with a unitary involution over a local field are commutative

This module proves `Langlands.LocalUnitaryDivisionCommutativeStatement`: over a
nonarchimedean local field `K`, a finite-dimensional central division algebra over a separable
quadratic extension `L` of `K` that carries a unitary involution has dimension one over `L`.
-/

noncomputable section

namespace Langlands

universe u

open ValuativeRel

section Aut

variable (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [Algebra K L] [FiniteDimensional K L]

local instance : NontriviallyNormedField K := LocalGalois.localNormedField K
local instance : CompleteSpace K := LocalGalois.localNormedField_complete K
local instance : IsUltrametricDist K := LocalGalois.localNormedField_ultrametric K

/-- `K`-automorphisms preserve the spectral valuation of a finite extension. -/
theorem finiteExtension_valuation_aut (σ : L ≃ₐ[K] L) (c : L) :
    letI := LocalField.FiniteExtension.valuativeRel K L
    valuation L (σ c) = valuation L c := by
  let := LocalField.FiniteExtension.valuativeRel K L
  have h : LocalGalois.spectralValuation K L (σ c) = LocalGalois.spectralValuation K L c :=
    NNReal.eq (spectralNorm_eq_of_equiv σ c).symm
  apply le_antisymm
  · rw [← (valuation L).vle_iff_le]
    exact h.le
  · rw [← (valuation L).vle_iff_le]
    exact h.ge

end Aut

/-- **Local unitary division algebras are commutative.** -/
theorem localUnitaryDivisionCommutative : LocalUnitaryDivisionCommutativeStatement.{u} := by
  intro K _ _ _ _ L _ _ _ _ σ hσ1 D _ _ _ _ τ hτ
  have hrank : Module.finrank K L = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
  have : FiniteDimensional K L := Module.finite_of_finrank_pos (by rw [hrank]; norm_num)
  let : ValuativeRel L := LocalField.FiniteExtension.valuativeRel K L
  let : TopologicalSpace L :=
    (LocalField.FiniteExtension.normedField K L).toUniformSpace.toTopologicalSpace
  have : IsNonarchimedeanLocalField L := LocalField.FiniteExtension.isLocalField K L
  let : Algebra K D := Algebra.compHom D (algebraMap K L)
  have : IsScalarTower K L D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let σr : L →+* L := σ.toRingHom
  have hτ' : IsUnitaryInvolution (⇑σr) τ := hτ
  have hσv : ∀ c, valuation L (σr c) = valuation L c := finiteExtension_valuation_aut K L σ
  have hσK : ∀ k : K, σr (algebraMap K L k) = algebraMap K L k := σ.commutes
  have hσσ : ∀ c, σr (σr c) = c := UnitaryInvolution.sigma_invol hτ'
  obtain ⟨θ, hθ⟩ : ∃ θ, σr θ ≠ θ := by
    by_contra h
    push Not at h
    exact hσ1 (AlgEquiv.ext h)
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, hrank]
  have hfix : ∀ ℓ : L, σr ℓ = ℓ → ∃ k : K, algebraMap K L k = ℓ := by
    intro ℓ hℓ
    have hall : ∀ f : L ≃ₐ[K] L, f ℓ = ℓ := by
      intro f
      by_cases hf1 : f = 1
      · rw [hf1]
        rfl
      by_cases hfσ : f = σ
      · rw [hfσ]
        exact hℓ
      exfalso
      classical
      have : Finite (L ≃ₐ[K] L) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
      let := Fintype.ofFinite (L ≃ₐ[K] L)
      have h3 : ({1, σ, f} : Finset (L ≃ₐ[K] L)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hfσ)]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hσ1, Ne.symm hf1⟩
      have h4 := Finset.card_le_univ ({1, σ, f} : Finset (L ≃ₐ[K] L))
      rw [Fintype.card_eq_nat_card, hcard, h3] at h4
      omega
    exact (IsGalois.mem_range_algebraMap_iff_fixed ℓ).mpr hall
  have hKL : ∀ a b : K, valuation L (algebraMap K L a) ≤ valuation L (algebraMap K L b) ↔
      valuation K a ≤ valuation K b := by
    intro a b
    rw [← (valuation L).vle_iff_le, ← (valuation K).vle_iff_le]
    exact LocalField.FiniteExtension.algebraMap_vle_iff K L a b
  have hdvd := UnitaryInvolution.reducedDegree_dvd_two hσv hτ'
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hd1 | hd2
  · rw [(CentralSimple.reducedNorm_degree_spec L D).2, hd1]
  · exfalso
    by_cases hsq : ∀ c : K, c ≠ 0 → ∃ ℓ : L, ℓ ≠ 0 ∧
        valuation L (algebraMap K L c) = valuation L ℓ ^ 2
    · exact UnitaryInvolution.false_of_valuation_squares hd2 hτ' hσK hθ hfix hrank hKL hsq
    · push Not at hsq
      obtain ⟨θ', h1, h2⟩ :=
        LocalQuadratic.exists_moved_of_not_squares hσv hσK hσσ hfix hKL hsq θ hθ
      exact UnitaryInvolution.false_of_residue_moved hσv hτ' hd2 θ' h1 h2

end Langlands
