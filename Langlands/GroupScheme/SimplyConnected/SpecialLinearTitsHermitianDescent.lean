import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsOuterDiscrepancy
import Langlands.LinearAlgebra.SpecialLinearProjectiveDescent

/-! # A Hermitian form from an outer discrepancy over a finite Galois cover -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearTitsCocycle

open Matrix
open Langlands.LinearAlgebra.SpecialLinearInverseTranspose
open Langlands.LinearAlgebra.SpecialLinearConjugation
open Langlands.LinearAlgebra.SpecialLinearHermitianNormalization
open Langlands.LinearAlgebra.SpecialLinearProjectiveDescent

variable {K L M : Type u} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M]
  {G : GroupScheme (Spec (CommRingCat.of K))} {n : ℕ}
  (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
    (cover K M))

omit E in
/-- An automorphism restricting to an involution has square in the range fixer. -/
theorem square_mem_fixingSubgroup_of_involution (f : L →ₐ[K] M)
    (c : SU3Root.RingInvolution L) (σ : M ≃ₐ[K] M)
    (hσ : ∀ z : L, σ (f z) = f (c.bar z)) :
    σ * σ ∈ f.fieldRange.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  rintro _ ⟨z, rfl⟩
  change σ (σ (f z)) = f z
  rw [hσ, hσ, c.bar_bar]

omit E in
/-- Automorphisms with the same restriction differ by an element of the range fixer. -/
theorem inv_mul_mem_fixingSubgroup_of_restriction (f : L →ₐ[K] M)
    {σ τ : M ≃ₐ[K] M} (hστ : ∀ z : L, τ (f z) = σ (f z)) :
    σ⁻¹ * τ ∈ f.fieldRange.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  rintro _ ⟨z, rfl⟩
  change σ.symm (τ (f z)) = f z
  rw [hστ, σ.symm_apply_apply]

variable [FiniteDimensional K M] [IsGalois K M] [IsGalois K L]

/-- Triviality on the range fixer descends an outer representative to that field,
up to a coefficient scalar, without losing any test scheme. -/
theorem HasOuterDiscrepancy.exists_field_representative (f : L →ₐ[K] M)
    (hH : HasTrivialDiscrepancy E f.fieldRange.fixingSubgroup)
    {σ : M ≃ₐ[K] M} {X : GeneralLinearGroup (Fin (n + 1)) M}
    (hX : HasOuterDiscrepancy E σ X) :
    ∃ Y : GeneralLinearGroup (Fin (n + 1)) L,
      HasOuterDiscrepancy E σ (GeneralLinearGroup.map f.toRingHom Y) := by
  have : IsGalois K f.fieldRange := IsGalois.of_algEquiv f.equivFieldRange
  obtain ⟨Y, b, hY⟩ := exists_projective_descent_galois f X (by
    intro τ g
    exact (hX.map_of_trivial E hH τ).conjugation_eq E hX g)
  refine ⟨Y, ?_⟩
  rw [hY]
  exact hX.scalar_mul E b

/-- A descended outer representative whose square is inner is the inverse Gram
matrix of a Hermitian form, up to scalars that preserve every test action. -/
theorem exists_hermitian_outer_representative (f : L →ₐ[K] M)
    (c : SU3Root.RingInvolution L) (hnontrivial : ∃ z : L, c.bar z ≠ z)
    (hH : HasTrivialDiscrepancy E f.fieldRange.fixingSubgroup)
    (σ : M ≃ₐ[K] M) (hσ : ∀ z : L, σ (f z) = f (c.bar z))
    (X : GeneralLinearGroup (Fin (n + 1)) M) (hX : HasOuterDiscrepancy E σ X) :
    ∃ J : HermitianMatrix.Form c (Fin (n + 1)),
      ∀ (τ : M ≃ₐ[K] M), (∀ z : L, τ (f z) = f (c.bar z)) →
        HasOuterDiscrepancy E τ (GeneralLinearGroup.map f.toRingHom J.gram⁻¹) := by
  obtain ⟨Y, hY⟩ := hX.exists_field_representative E f hH
  have hbar : GeneralLinearGroup.map σ.toRingHom (GeneralLinearGroup.map f.toRingHom Y) =
      GeneralLinearGroup.map f.toRingHom (GeneralLinearGroup.map c.bar.toRingHom Y) := by
    apply Units.ext
    ext i j
    exact hσ (Y i j)
  obtain ⟨b, hb⟩ := hY.exists_scalar_square E hH
    (square_mem_fixingSubgroup_of_involution f c σ hσ)
  have hm : GeneralLinearGroup.map f.toRingHom
      (Y * inverseTransposeGL (GeneralLinearGroup.map c.bar.toRingHom Y)) =
        GeneralLinearGroup.scalar (Fin (n + 1)) b := by
    rw [map_mul, ← inverseTransposeGL_map, ← hbar]
    exact hb
  obtain ⟨a, ha⟩ := exists_scalar_of_map_eq_scalar f.toRingHom _ b hm
  have hJ := inverse_adjoint_of_outer_square c Y a ha
  let J := hermitianForm c hnontrivial Y⁻¹ (a : L) hJ
  have hrepr : HasOuterDiscrepancy E σ (GeneralLinearGroup.map f.toRingHom J.gram⁻¹) := by
    intro Z q g
    have he := hermitianForm_inverse_conjugate ((coefficients q).comp f.toRingHom)
      c hnontrivial Y⁻¹ (a : L) hJ (SpecialLinearGroup.toGL (inverseTranspose g))
    change _ = GeneralLinearGroup.map ((coefficients q).comp f.toRingHom) J.gram⁻¹ *
      SpecialLinearGroup.toGL (inverseTranspose g) *
      (GeneralLinearGroup.map ((coefficients q).comp f.toRingHom) J.gram⁻¹)⁻¹
    rw [he]
    have hcomp (Q : GeneralLinearGroup (Fin (n + 1)) L) :
        GeneralLinearGroup.map ((coefficients q).comp f.toRingHom) Q =
          GeneralLinearGroup.map (coefficients q) (GeneralLinearGroup.map f.toRingHom Q) := by
      apply Units.ext
      rfl
    simpa only [inv_inv, hcomp] using hY Z q g
  refine ⟨J, fun τ hτ => ?_⟩
  exact hrepr.of_inv_mul_mem E hH
    (inv_mul_mem_fixingSubgroup_of_restriction f (fun z => (hτ z).trans (hσ z).symm))

/-- The chosen nonsingular Hermitian form supplied by an outer representative. -/
def outerHermitianForm (f : L →ₐ[K] M)
    (c : SU3Root.RingInvolution L) (hnontrivial : ∃ z : L, c.bar z ≠ z)
    (hH : HasTrivialDiscrepancy E f.fieldRange.fixingSubgroup)
    (σ : M ≃ₐ[K] M) (hσ : ∀ z : L, σ (f z) = f (c.bar z))
    (X : GeneralLinearGroup (Fin (n + 1)) M) (hX : HasOuterDiscrepancy E σ X) :
    HermitianMatrix.Form c (Fin (n + 1)) :=
  Classical.choose (exists_hermitian_outer_representative E f c hnontrivial hH σ hσ X hX)

/-- Its inverse Gram matrix represents every automorphism restricting to the
specified nontrivial involution, on every relative test scheme. -/
theorem outerHermitianForm_spec (f : L →ₐ[K] M)
    (c : SU3Root.RingInvolution L) (hnontrivial : ∃ z : L, c.bar z ≠ z)
    (hH : HasTrivialDiscrepancy E f.fieldRange.fixingSubgroup)
    (σ : M ≃ₐ[K] M) (hσ : ∀ z : L, σ (f z) = f (c.bar z))
    (X : GeneralLinearGroup (Fin (n + 1)) M) (hX : HasOuterDiscrepancy E σ X)
    (τ : M ≃ₐ[K] M) (hτ : ∀ z : L, τ (f z) = f (c.bar z)) :
    HasOuterDiscrepancy E τ (GeneralLinearGroup.map f.toRingHom
      (outerHermitianForm E f c hnontrivial hH σ hσ X hX).gram⁻¹) :=
  Classical.choose_spec (exists_hermitian_outer_representative E f c hnontrivial hH σ hσ X hX)
    τ hτ

end Langlands.GroupScheme.SpecialLinearTitsCocycle
