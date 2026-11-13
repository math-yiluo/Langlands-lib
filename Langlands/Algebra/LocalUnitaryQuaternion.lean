import Langlands.Algebra.QuaternionUnitaryDescent
import Langlands.Algebra.LocalUnitaryResidue

/-!
# Quaternion division algebras with unitary involutions over local fields: the descent case

Let `L/K` be a quadratic extension of nonarchimedean local fields and `D` a central division
`L`-algebra of reduced degree `2` with a unitary involution. Applying the local theory to the
descended algebra `D₀` produces a unit of `D` fixed by `β = τ ∘ γ` whose conjugation acts
nontrivially on the residue field of `D`. If every element of `K` has the valuation of a square
of an element of `L` (which happens when `L/K` is ramified), this is impossible.
-/

noncomputable section

namespace Langlands.UnitaryInvolution

universe u

open Langlands.CentralDivision Langlands.CentralSimple Langlands.DivisionValuation ValuativeRel
open scoped TensorProduct

variable {K L D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
  [DivisionRing D] [Algebra L D] [FiniteDimensional L D] [Algebra.IsCentral L D]
  [Algebra K D] [IsScalarTower K L D] {σ : L →+* L} {τ : D → D}
  (hd : reducedDegree L D = 2) (hτ : IsUnitaryInvolution (⇑σ) τ)
  (hσK : ∀ k : K, σ (algebraMap K L k) = algebraMap K L k)
  {θ : L} (hθ : σ θ ≠ θ) (hfix : ∀ ℓ : L, σ ℓ = ℓ → ∃ k : K, algebraMap K L k = ℓ)
  (hrank : Module.finrank K L = 2)
  (hKL : ∀ a b : K, valuation L (algebraMap K L a) ≤ valuation L (algebraMap K L b) ↔
    valuation K a ≤ valuation K b)
include hd hτ hσK hθ hfix hrank hKL

/-- A unit of `D`, fixed by `β`, acting nontrivially on the residue field by conjugation. -/
theorem exists_fixed_unit_conj_nontrivial :
    ∃ U : Dˣ, beta L τ (U : D) = U ∧ ∃ w : D, localReducedNormValuation L D w ≤ 1 ∧
      ¬ localReducedNormValuation L D ((U : D) * w * ((U⁻¹ : Dˣ) : D) - w) < 1 := by
  let D₀ := fixedSubalgebra hd hτ hσK
  let := fixedDivisionRing hd hτ hσK
  let := fixed_finiteDimensional hd hτ hσK
  let := fixed_isCentral hd hτ hσK hθ hfix
  have hd0 := reducedDegree_fixed hd hτ hσK hθ hrank
  have hle1 : ∀ a : K, valuation L (algebraMap K L a) ≤ 1 ↔ valuation K a ≤ 1 := by
    intro a
    simpa using hKL a 1
  have hlt1 : ∀ a : K, valuation L (algebraMap K L a) < 1 ↔ valuation K a < 1 := by
    intro a
    have h := hKL 1 a
    simp only [map_one] at h
    rw [← not_le, ← not_le, h]
  have hle : ∀ y : D₀, localReducedNormValuation L D (y : D) ≤ 1 ↔
      localReducedNormValuation K D₀ y ≤ 1 := by
    intro y
    rw [localReducedNormValuation_apply, localReducedNormValuation_apply]
    change valuation L (nrd L (y : D)) ≤ 1 ↔ valuation K (nrd K y) ≤ 1
    rw [nrd_fixed hd hτ hσK hθ hfix hrank y]
    exact hle1 _
  have hlt : ∀ y : D₀, localReducedNormValuation L D (y : D) < 1 ↔
      localReducedNormValuation K D₀ y < 1 := by
    intro y
    rw [localReducedNormValuation_apply, localReducedNormValuation_apply]
    change valuation L (nrd L (y : D)) < 1 ↔ valuation K (nrd K y) < 1
    rw [nrd_fixed hd hτ hσK hθ hfix hrank y]
    exact hlt1 _
  obtain ⟨u₀, hu₀⟩ := exists_unit_conjResidue_faithful K D₀
  have hnot : ¬ ∀ r, conjResidue (localReducedNormValuation K D₀) (u₀ ^ 1) r = r := by
    intro h
    have := hu₀ 1 h
    rw [hd0] at this
    norm_num at this
  push Not at hnot
  obtain ⟨r, hr⟩ := hnot
  obtain ⟨w₀, rfl⟩ := reduction_surjective _ r
  rw [pow_one, conjResidue_reduction, Ne, reduction_eq_iff] at hr
  let U : Dˣ := Units.map (D₀.val : D₀ →* D) u₀
  refine ⟨U, (u₀ : D₀).prop, ((w₀ : D₀) : D), (hle w₀).mpr w₀.prop, ?_⟩
  have hcoe : (U : D) * ((w₀ : D₀) : D) * ((U⁻¹ : Dˣ) : D) - ((w₀ : D₀) : D) =
      (((conjInteger (localReducedNormValuation K D₀) u₀ w₀ : D₀) - (w₀ : D₀) : D₀) : D) := by
    rw [conjInteger_coe]
    rfl
  rw [hcoe, hlt]
  exact hr

/-- **Descent case.** If every element of `K` has the valuation of a square of an element of
`L`, then no central division `L`-algebra of reduced degree `2` carries a unitary involution. -/
theorem false_of_valuation_squares
    (hsq : ∀ c : K, c ≠ 0 → ∃ ℓ : L, ℓ ≠ 0 ∧
      valuation L (algebraMap K L c) = valuation L ℓ ^ 2) : False := by
  obtain ⟨U, hU, w, hw, hne⟩ := exists_fixed_unit_conj_nontrivial hd hτ hσK hθ hfix hrank hKL
  let v := localReducedNormValuation L D
  have hnrd : σ (nrd L (U : D)) = nrd L (U : D) := by
    rw [← nrd_beta hd hτ, hU]
  obtain ⟨c, hc⟩ := hfix _ hnrd
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact nrd_ne_zero U.ne_zero hc.symm
  obtain ⟨ℓ, hℓ0, hℓ⟩ := hsq c hc0
  let Uℓ : Dˣ := Units.mk0 (algebraMap L D ℓ) ((map_ne_zero_iff _ (algebraMap L D).injective).mpr hℓ0)
  have hvU : v (Uℓ : D) = v (U : D) := by
    change localReducedNormValuation L D (algebraMap L D ℓ) =
      valuation L (reducedNorm L D L (1 ⊗ₜ[L] (U : D)))
    rw [localReducedNormValuation_algebraMap, hd]
    change valuation L ℓ ^ 2 = valuation L (nrd L (U : D))
    rw [← hc, hℓ]
  have hcomm : ∀ a b : Residue v, a * b = b * a := localDivisionResidue_mul_comm L D
  have hcentral : ∀ r, conjResidue v Uℓ r = r := by
    intro r
    obtain ⟨x, rfl⟩ := reduction_surjective v r
    rw [conjResidue_reduction]
    congr 1
    apply Subtype.ext
    rw [conjInteger_coe]
    change algebraMap L D ℓ * (x : D) * (algebraMap L D ℓ)⁻¹ = x
    rw [Algebra.commutes, mul_assoc, mul_inv_cancel₀
      ((map_ne_zero_iff _ (algebraMap L D).injective).mpr hℓ0), mul_one]
  let wI : v.integer := ⟨w, hw⟩
  have h := conjResidue_eq_of_value_eq v hcomm Uℓ U hvU (reduction v wI)
  rw [hcentral, conjResidue_reduction, reduction_eq_iff] at h
  exact hne h

end Langlands.UnitaryInvolution
