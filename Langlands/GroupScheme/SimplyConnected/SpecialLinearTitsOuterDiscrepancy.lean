import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCoordinateChange
import Langlands.LinearAlgebra.SpecialLinearHermitianNormalization

/-! # Outer discrepancies after trivialising the inner subgroup -/

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
open Langlands.LinearAlgebra.SpecialLinearHermitianNormalization

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {G : GroupScheme (Spec (CommRingCat.of K))} {n : ℕ}
  (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
    (cover K L))

/-- All discrepancies of a specified subgroup are the identity on every test. -/
def HasTrivialDiscrepancy (H : Subgroup (L ≃ₐ[K] L)) : Prop :=
  ∀ (σ : H) (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K L)
    (g : SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)),
    discrepancy E σ.val a g = g

/-- Products of two outer discrepancies have the expected inner representative. -/
theorem HasOuterDiscrepancy.mul_outer {σ τ : L ≃ₐ[K] L}
    {X Y : GeneralLinearGroup (Fin (n + 1)) L}
    (hX : HasOuterDiscrepancy E σ X) (hY : HasOuterDiscrepancy E τ Y) :
    HasInnerDiscrepancy E (σ * τ)
      (X * inverseTransposeGL (GeneralLinearGroup.map σ.toRingHom Y)) := by
  intro Z a g
  rw [discrepancy_mul, hX, toGL_inverseTranspose, hY, coefficients_coverAut,
    toGL_inverseTranspose]
  change GeneralLinearGroup.map (coefficients a) X *
      inverseTransposeGL
        (GeneralLinearGroup.map (coefficients a) (GeneralLinearGroup.map σ.toRingHom Y) *
          inverseTransposeGL (SpecialLinearGroup.toGL g) *
          (GeneralLinearGroup.map (coefficients a) (GeneralLinearGroup.map σ.toRingHom Y))⁻¹) *
      (GeneralLinearGroup.map (coefficients a) X)⁻¹ = _
  simp only [map_mul, map_inv, inverseTransposeGL_involutive, inverseTransposeGL_map]
  group

/-- A scalar multiple of an outer representative gives the same all-test action. -/
theorem HasOuterDiscrepancy.scalar_mul {σ : L ≃ₐ[K] L}
    {X : GeneralLinearGroup (Fin (n + 1)) L}
    (hX : HasOuterDiscrepancy E σ X) (b : Lˣ) :
    HasOuterDiscrepancy E σ (GeneralLinearGroup.scalar (Fin (n + 1)) b * X) := by
  intro Z a g
  rw [map_scalar_mul_conjugate]
  exact hX Z a g

/-- Equal all-test outer actions give equal conjugations on the special linear group. -/
theorem HasOuterDiscrepancy.conjugation_eq {σ : L ≃ₐ[K] L}
    {X Y : GeneralLinearGroup (Fin (n + 1)) L}
    (hX : HasOuterDiscrepancy E σ X) (hY : HasOuterDiscrepancy E σ Y)
    (g : SpecialLinearGroup (Fin (n + 1)) L) :
    X * SpecialLinearGroup.toGL g * X⁻¹ = Y * SpecialLinearGroup.toGL g * Y⁻¹ := by
  let f := (baseCoefficientsEquiv (K := K) (L := L)).toRingHom
  have h := (hX _ (𝟙 _) (SpecialLinearGroup.map f (inverseTranspose g))).symm.trans
    (hY _ (𝟙 _) (SpecialLinearGroup.map f (inverseTranspose g)))
  rw [coefficients_id, inverseTranspose_map, toGL_map, toGL_inverseTranspose,
    toGL_inverseTranspose, inverseTransposeGL_involutive] at h
  change GeneralLinearGroup.map f X * GeneralLinearGroup.map f (SpecialLinearGroup.toGL g) *
      (GeneralLinearGroup.map f X)⁻¹ =
    GeneralLinearGroup.map f Y * GeneralLinearGroup.map f (SpecialLinearGroup.toGL g) *
      (GeneralLinearGroup.map f Y)⁻¹ at h
  simp only [← map_inv, ← map_mul] at h
  apply Units.ext
  ext i j
  apply (baseCoefficientsEquiv (K := K) (L := L)).injective
  exact congrArg (fun z : GeneralLinearGroup (Fin (n + 1)) Γ((cover K L).left, ⊤) =>
    z i j) h

variable {H : Subgroup (L ≃ₐ[K] L)}

/-- Right multiplication by an element with trivial discrepancy changes no action. -/
theorem HasTrivialDiscrepancy.mul_right (hH : HasTrivialDiscrepancy E H)
    (σ : L ≃ₐ[K] L) (τ : H) {Z : Over (Spec (CommRingCat.of K))}
    (a : Z ⟶ cover K L) (g : SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
    discrepancy E (σ * τ.val) a g = discrepancy E σ a g := by
  rw [discrepancy_mul, hH τ]

/-- Automorphisms in the same left coset of the trivial subgroup have equal actions. -/
theorem HasTrivialDiscrepancy.eq_of_inv_mul_mem (hH : HasTrivialDiscrepancy E H)
    {σ τ : L ≃ₐ[K] L} (hστ : σ⁻¹ * τ ∈ H)
    {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K L)
    (g : SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
    discrepancy E τ a g = discrepancy E σ a g := by
  simpa only [mul_inv_cancel_left] using hH.mul_right E σ ⟨_, hστ⟩ a g

/-- For a normal trivial subgroup, the action is independent of its shift of the cover point. -/
theorem HasTrivialDiscrepancy.coverAut [H.Normal] (hH : HasTrivialDiscrepancy E H)
    (σ : L ≃ₐ[K] L) (τ : H) {Z : Over (Spec (CommRingCat.of K))}
    (a : Z ⟶ cover K L) (g : SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
    discrepancy E σ (a ≫ coverAut K L τ.val) g = discrepancy E σ a g := by
  have hconj : σ⁻¹ * τ.val * σ ∈ H := by
    exact Subgroup.Normal.conj_mem' inferInstance τ.val τ.property σ
  have heq : σ⁻¹ * (τ.val * σ) ∈ H := by
    simpa only [mul_assoc] using hconj
  have h := hH.eq_of_inv_mul_mem E heq a g
  rw [discrepancy_mul, hH τ] at h
  exact h

/-- Over a normal trivial subgroup, conjugating coefficients preserves an outer representative. -/
theorem HasOuterDiscrepancy.map_of_trivial [H.Normal]
    (hH : HasTrivialDiscrepancy E H) {σ : L ≃ₐ[K] L}
    {X : GeneralLinearGroup (Fin (n + 1)) L} (hX : HasOuterDiscrepancy E σ X)
    (τ : H) :
    HasOuterDiscrepancy E σ (GeneralLinearGroup.map τ.val.toRingHom X) := by
  intro Z a g
  have h := hX Z (a ≫ coverAut K L τ.val) g
  rw [hH.coverAut E σ τ a g, coefficients_coverAut] at h
  exact h

/-- A representative works for every automorphism in the same left coset. -/
theorem HasOuterDiscrepancy.of_inv_mul_mem (hH : HasTrivialDiscrepancy E H)
    {σ τ : L ≃ₐ[K] L} {X : GeneralLinearGroup (Fin (n + 1)) L}
    (hX : HasOuterDiscrepancy E σ X) (hστ : σ⁻¹ * τ ∈ H) :
    HasOuterDiscrepancy E τ X := by
  intro Z a g
  rw [hH.eq_of_inv_mul_mem E hστ]
  exact hX Z a g

/-- If the square lies in the trivial subgroup, the semilinear outer square is scalar. -/
theorem HasOuterDiscrepancy.exists_scalar_square (hH : HasTrivialDiscrepancy E H)
    {σ : L ≃ₐ[K] L} {X : GeneralLinearGroup (Fin (n + 1)) L}
    (hX : HasOuterDiscrepancy E σ X) (hσ : σ * σ ∈ H) :
    ∃ b : Lˣ, X * inverseTransposeGL (GeneralLinearGroup.map σ.toRingHom X) =
      GeneralLinearGroup.scalar (Fin (n + 1)) b := by
  have hm := hX.mul_outer E hX
  have hi : HasInnerDiscrepancy E (σ * σ) 1 := by
    intro Z a g
    rw [hH ⟨_, hσ⟩]
    simp
  obtain ⟨b, hb⟩ := exists_unit_scalar_of_conjugation_eq
    (X * inverseTransposeGL (GeneralLinearGroup.map σ.toRingHom X)) (by
      intro g
      simpa using hm.conjugation_eq E hi g)
  exact ⟨b, hb.symm⟩

end Langlands.GroupScheme.SpecialLinearTitsCocycle
