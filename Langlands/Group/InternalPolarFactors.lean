import Langlands.Group.AlgebraicPolar
import Langlands.Group.ClosedPolarCompact

/-! # Polar factors in polynomially defined self-adjoint matrix groups -/

noncomputable section

universe u v

namespace Langlands.Group.InternalPolarFactors

open Matrix
open Langlands.Group.AlgebraicMatrixPowers
open Langlands.Group.AlgebraicPolar
open Langlands.Group.MatrixPolarCompact
open scoped ComplexOrder

variable {𝕜 : Type u} [RCLike 𝕜] {n : Type} [Fintype n] [DecidableEq n]

/-- A polynomially defined subgroup closed under adjoints contains the unitary
and positive definite factors of each of its elements. -/
theorem exists_unitary_posDef_factors (H : Subgroup (GL n 𝕜))
    (hH : IsPolynomiallyDefined H) (hstar : ∀ g ∈ H, star g ∈ H)
    (g : GL n 𝕜) (hg : g ∈ H) :
    ∃ k a : GL n 𝕜, k ∈ H ∧ a ∈ H ∧
      k.val ∈ Matrix.unitaryGroup n 𝕜 ∧ a.val.PosDef ∧ g = k * a := by
  have hpos : (star g * g).val.PosDef :=
    Matrix.PosDef.conjTranspose_mul_self g.val (Matrix.mulVec_injective_of_isUnit g.isUnit)
  obtain ⟨a, ha, hapos, haa⟩ := exists_positive_sqrt H hH (star g * g) hpos
    (H.mul_mem (hstar g hg) hg)
  have hsa : star a = a := Units.ext hapos.isHermitian.star_eq
  refine ⟨g * a⁻¹, a, H.mul_mem hg (H.inv_mem ha), ha, ?_, hapos, ?_⟩
  · apply (Units.mul_inv_mem_unitary g a).mpr
    rw [hsa, haa]
  · exact (inv_mul_cancel_right g a).symm

/-- The same factors can be arranged with the positive definite factor first. -/
theorem exists_posDef_unitary_factors (H : Subgroup (GL n 𝕜))
    (hH : IsPolynomiallyDefined H) (hstar : ∀ g ∈ H, star g ∈ H)
    (g : GL n 𝕜) (hg : g ∈ H) :
    ∃ a k : GL n 𝕜, a ∈ H ∧ k ∈ H ∧
      a.val.PosDef ∧ k.val ∈ Matrix.unitaryGroup n 𝕜 ∧ g = a * k := by
  obtain ⟨k, a, hk, ha, hku, hapos, hka⟩ :=
    exists_unitary_posDef_factors H hH hstar (star g) (hstar g hg)
  have hsa : star a = a := Units.ext hapos.isHermitian.star_eq
  refine ⟨a, star k, ha, hstar k hk, hapos, ?_, ?_⟩
  · simpa only [Units.coe_star] using Unitary.star_mem hku
  · calc
      g = star (star g) := (star_star g).symm
      _ = a * star k := by rw [hka, star_mul, hsa]

variable {A : Type v} [Group A] {d : ℕ}

/-- Transport right positive polar factors through a faithful representation. -/
theorem exists_unitary_posDef_factors_of_range
    (ρ : A →* GL (Fin d) 𝕜) (hinj : Function.Injective ρ)
    (hpoly : IsPolynomiallyDefined ρ.range)
    (hstar : ∀ g ∈ ρ.range, star g ∈ ρ.range) (g : A) :
    ∃ k a : A, k ∈ unitarySubgroup ρ ∧ (ρ a).val.PosDef ∧ g = k * a := by
  obtain ⟨k, a, hk, ha, hku, hapos, hka⟩ :=
    exists_unitary_posDef_factors ρ.range hpoly hstar (ρ g) ⟨g, rfl⟩
  obtain ⟨k₀, rfl⟩ := hk
  obtain ⟨a₀, rfl⟩ := ha
  exact ⟨k₀, a₀, (mem_unitarySubgroup ρ k₀).mpr hku, hapos,
    hinj (by simpa only [map_mul] using hka)⟩

/-- Transport left positive polar factors through a faithful representation. -/
theorem exists_posDef_unitary_factors_of_range
    (ρ : A →* GL (Fin d) 𝕜) (hinj : Function.Injective ρ)
    (hpoly : IsPolynomiallyDefined ρ.range)
    (hstar : ∀ g ∈ ρ.range, star g ∈ ρ.range) (g : A) :
    ∃ a k : A, (ρ a).val.PosDef ∧ k ∈ unitarySubgroup ρ ∧ g = a * k := by
  obtain ⟨a, k, ha, hk, hapos, hku, hak⟩ :=
    exists_posDef_unitary_factors ρ.range hpoly hstar (ρ g) ⟨g, rfl⟩
  obtain ⟨a₀, rfl⟩ := ha
  obtain ⟨k₀, rfl⟩ := hk
  exact ⟨a₀, k₀, hapos, (mem_unitarySubgroup ρ k₀).mpr hku,
    hinj (by simpa only [map_mul] using hak)⟩

/-- Every element has a positive definite right quotient by a unitary element. -/
theorem exists_unitary_right_quotient_posDef
    (ρ : A →* GL (Fin d) 𝕜) (hinj : Function.Injective ρ)
    (hpoly : IsPolynomiallyDefined ρ.range)
    (hstar : ∀ g ∈ ρ.range, star g ∈ ρ.range) (g : A) :
    ∃ k : A, k ∈ unitarySubgroup ρ ∧ (ρ (g * k⁻¹)).val.PosDef := by
  obtain ⟨a, k, hapos, hk, hak⟩ :=
    exists_posDef_unitary_factors_of_range ρ hinj hpoly hstar g
  refine ⟨k, hk, ?_⟩
  simpa only [hak, mul_inv_cancel_right] using hapos

variable [TopologicalSpace A]

/-- Construct a maximal compact subgroup from a closed faithful representation
whose image is polynomially defined and closed under adjoints. -/
def maximalCompactOfPolynomialStarClosed
    (ρ : A →* GL (Fin d) 𝕜) (hρ : Topology.IsClosedEmbedding ρ)
    (hpoly : IsPolynomiallyDefined ρ.range)
    (hstar : ∀ g ∈ ρ.range, star g ∈ ρ.range) :
    {K : Subgroup A // IsCompact (K : Set A) ∧
      ∀ L : Subgroup A, IsCompact (L : Set A) → K ≤ L → L = K} :=
  maximalCompactOfClosedPolar ρ hρ fun g => by
    obtain ⟨k, a, hk, hapos, hka⟩ :=
      exists_unitary_posDef_factors_of_range ρ hρ.injective hpoly hstar g
    exact ⟨k, a, hk, hapos.posSemidef, hka⟩

end Langlands.Group.InternalPolarFactors
