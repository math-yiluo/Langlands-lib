import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsOuterDiscrepancy

/-! # Mixed products of inner and outer discrepancies and the twisted cocycle law -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearTitsCocycle

open Matrix
open Langlands.LinearAlgebra.SpecialLinearConjugation
open Langlands.LinearAlgebra.SpecialLinearInverseTranspose

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {G : GroupScheme (Spec (CommRingCat.of K))} {n : ℕ}
  (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
    (cover K L))

/-- An inner discrepancy followed by an outer one has the semilinear product as an
outer representative. -/
theorem HasInnerDiscrepancy.mul_outer {σ τ : L ≃ₐ[K] L}
    {X Y : GeneralLinearGroup (Fin (n + 1)) L}
    (hX : HasInnerDiscrepancy E σ X) (hY : HasOuterDiscrepancy E τ Y) :
    HasOuterDiscrepancy E (σ * τ) (X * GeneralLinearGroup.map σ.toRingHom Y) := by
  intro Z a g
  rw [discrepancy_mul, hX, hY, coefficients_coverAut]
  have hmap : GeneralLinearGroup.map ((coefficients a).comp σ.toRingHom) Y =
      GeneralLinearGroup.map (coefficients a) (GeneralLinearGroup.map σ.toRingHom Y) := rfl
  rw [hmap, map_mul]
  group

/-- An outer discrepancy followed by an inner one has the inverse-transposed semilinear
product as an outer representative. -/
theorem HasOuterDiscrepancy.mul_inner {σ τ : L ≃ₐ[K] L}
    {X Y : GeneralLinearGroup (Fin (n + 1)) L}
    (hX : HasOuterDiscrepancy E σ X) (hY : HasInnerDiscrepancy E τ Y) :
    HasOuterDiscrepancy E (σ * τ)
      (X * inverseTransposeGL (GeneralLinearGroup.map σ.toRingHom Y)) := by
  intro Z a g
  rw [discrepancy_mul, hX, toGL_inverseTranspose, hY, coefficients_coverAut]
  change GeneralLinearGroup.map (coefficients a) X *
      inverseTransposeGL
        (GeneralLinearGroup.map (coefficients a) (GeneralLinearGroup.map σ.toRingHom Y) *
          SpecialLinearGroup.toGL g *
          (GeneralLinearGroup.map (coefficients a) (GeneralLinearGroup.map σ.toRingHom Y))⁻¹) *
      (GeneralLinearGroup.map (coefficients a) X)⁻¹ = _
  simp only [map_mul, map_inv, toGL_inverseTranspose, inverseTransposeGL_map]
  group

omit E in
/-- Right multiplication by an invertible scalar is scalar multiplication of the matrix. -/
theorem coe_mul_scalar (Z : GeneralLinearGroup (Fin (n + 1)) L) (c : Lˣ) :
    ((Z * GeneralLinearGroup.scalar (Fin (n + 1)) c : GeneralLinearGroup (Fin (n + 1)) L) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) L) =
      (c : L) • (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) L) := by
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

omit E in
/-- The matrix of the semilinear product `X * σ(Y)`. -/
theorem coe_mul_map (σ : L ≃ₐ[K] L) (X Y : GeneralLinearGroup (Fin (n + 1)) L) :
    ((X * GeneralLinearGroup.map σ.toRingHom Y : GeneralLinearGroup (Fin (n + 1)) L) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) L) =
      (X : Matrix (Fin (n + 1)) (Fin (n + 1)) L) *
        (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) L).map σ := rfl

omit E in
/-- The matrix of the twisted product `X * σ(Y)⁻ᵀ`. -/
theorem coe_mul_inverseTranspose_map (σ : L ≃ₐ[K] L)
    (X Y : GeneralLinearGroup (Fin (n + 1)) L) :
    ((X * inverseTransposeGL (GeneralLinearGroup.map σ.toRingHom Y) :
        GeneralLinearGroup (Fin (n + 1)) L) : Matrix (Fin (n + 1)) (Fin (n + 1)) L) =
      (X : Matrix (Fin (n + 1)) (Fin (n + 1)) L) *
        ((((Y⁻¹ : GeneralLinearGroup (Fin (n + 1)) L)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) L).map σ)ᵀ := by
  rw [Units.val_mul, coe_inverseTransposeGL, ← map_inv]
  rfl

/-- The matrix-level twisted projective cocycle law for a family `x` of invertible
matrices indexed by `L ≃ₐ[K] L` and an index-two subgroup `H`: on `H` the family is a
semilinear cocycle up to scalars, and off `H` the second factor is replaced by its
semilinear inverse transpose. -/
def IsTwistedProjectiveCocycle (H : Subgroup (L ≃ₐ[K] L))
    (x : (L ≃ₐ[K] L) → GeneralLinearGroup (Fin (n + 1)) L) : Prop :=
  (∀ σ ∈ H, ∀ τ, ∃ c : Lˣ, (x (σ * τ) : Matrix (Fin (n + 1)) (Fin (n + 1)) L) =
      (c : L) • ((x σ : Matrix (Fin (n + 1)) (Fin (n + 1)) L) *
        (x τ : Matrix (Fin (n + 1)) (Fin (n + 1)) L).map σ)) ∧
  (∀ σ ∉ H, ∀ τ, ∃ c : Lˣ, (x (σ * τ) : Matrix (Fin (n + 1)) (Fin (n + 1)) L) =
      (c : L) • ((x σ : Matrix (Fin (n + 1)) (Fin (n + 1)) L) *
        ((((x τ)⁻¹ : GeneralLinearGroup (Fin (n + 1)) L) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) L).map σ)ᵀ))

/-- Inner representatives on an index-two subgroup and outer representatives off it
satisfy the twisted projective cocycle law. -/
theorem isTwistedProjectiveCocycle_of_discrepancy {H : Subgroup (L ≃ₐ[K] L)}
    {x : (L ≃ₐ[K] L) → GeneralLinearGroup (Fin (n + 1)) L} (hH : H.index = 2)
    (hI : ∀ σ ∈ H, HasInnerDiscrepancy E σ (x σ))
    (hO : ∀ σ ∉ H, HasOuterDiscrepancy E σ (x σ)) :
    IsTwistedProjectiveCocycle H x := by
  have hmem (σ τ : L ≃ₐ[K] L) : σ * τ ∈ H ↔ (σ ∈ H ↔ τ ∈ H) :=
    Subgroup.mul_mem_iff_of_index_two hH
  constructor
  · intro σ hσ τ
    rw [← coe_mul_map]
    by_cases hτ : τ ∈ H
    · have hστ : σ * τ ∈ H := (hmem σ τ).2 (iff_of_true hσ hτ)
      obtain ⟨c, hc⟩ := exists_unit_scalar_of_conjugation_eq_conjugation _ _
        ((hI _ hστ).conjugation_eq E ((hI σ hσ).mul E (hI τ hτ)))
      exact ⟨c, by rw [hc, coe_mul_scalar]⟩
    · have hστ : σ * τ ∉ H := fun h => hτ (((hmem σ τ).1 h).1 hσ)
      obtain ⟨c, hc⟩ := exists_unit_scalar_of_conjugation_eq_conjugation _ _
        ((hO _ hστ).conjugation_eq E ((hI σ hσ).mul_outer E (hO τ hτ)))
      exact ⟨c, by rw [hc, coe_mul_scalar]⟩
  · intro σ hσ τ
    rw [← coe_mul_inverseTranspose_map]
    by_cases hτ : τ ∈ H
    · have hστ : σ * τ ∉ H := fun h => hσ (((hmem σ τ).1 h).2 hτ)
      obtain ⟨c, hc⟩ := exists_unit_scalar_of_conjugation_eq_conjugation _ _
        ((hO _ hστ).conjugation_eq E ((hO σ hσ).mul_inner E (hI τ hτ)))
      exact ⟨c, by rw [hc, coe_mul_scalar]⟩
    · have hστ : σ * τ ∈ H := (hmem σ τ).2 (iff_of_false hσ hτ)
      obtain ⟨c, hc⟩ := exists_unit_scalar_of_conjugation_eq_conjugation _ _
        ((hI _ hστ).conjugation_eq E ((hO σ hσ).mul_outer E (hO τ hτ)))
      exact ⟨c, by rw [hc, coe_mul_scalar]⟩

end Langlands.GroupScheme.SpecialLinearTitsCocycle
