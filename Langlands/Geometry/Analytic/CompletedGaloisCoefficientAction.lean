import Langlands.Galois.Local.HodgeTate
import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionCoefficientAction
import Mathlib.Analysis.Normed.Module.Completion

/-! # The absolute Galois group on the completed algebraic closure -/

noncomputable section

open UniformSpace
open Langlands.GaloisRepresentation.HodgeTate
open Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension
open scoped Topology

set_option autoImplicit false

universe u

namespace Langlands.Analytic.CompletedGaloisCoefficientAction

variable (p : ℕ) [Fact p.Prime] (F : Type u)
variable [NormedField F] [NormedAlgebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- The norm on the algebraic closure extends the given norm of the finite
extension. Both extend the p-adic norm. -/
theorem norm_algebraMap_closure (x : F) : ‖algebraMap F (Closure p F) x‖ = ‖x‖ := by
  change spectralNorm ℚ_[p] (Closure p F) (algebraMap F (Closure p F) x) = ‖x‖
  rw [← spectralNorm.eq_of_tower, ← NormedAlgebra.norm_eq_spectralNorm ℚ_[p] x]

instance closureNormedAlgebra : NormedAlgebra F (Closure p F) where
  toAlgebra := inferInstance
  norm_smul_le x y := by rw [Algebra.smul_def, norm_mul, norm_algebraMap_closure]

instance closureUltrametric : IsUltrametricDist (Closure p F) := by
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
  exact isNonarchimedean_spectralNorm (K := ℚ_[p]) (L := Closure p F)

instance completedNormedAlgebra : NormedAlgebra F (Completed p F) :=
  inferInstanceAs (NormedAlgebra F (Completion (Closure p F)))

instance completedUltrametric : IsUltrametricDist (Completed p F) := by
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
  intro x y
  induction x, y using Completion.induction_on₂ with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih a b =>
    rw [← Completion.coe_add]
    simpa only [Completion.norm_coe] using IsUltrametricDist.norm_add_le_max a b

/-- The actual extension of the base field into its completed algebraic closure is isometric. -/
theorem norm_algebraMap_completed (x : F) : ‖algebraMap F (Completed p F) x‖ = ‖x‖ := by
  rw [Completion.algebraMap_def, Completion.norm_coe, norm_algebraMap_closure]

theorem isometry_algebraMap_completed : Isometry (algebraMap F (Completed p F)) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_algebraMap_completed p F)

/-- The extension of an absolute Galois element is an actual `F`-algebra automorphism. -/
def completedAutomorphism (σ : Field.absoluteGaloisGroup F) : Completed p F ≃ₐ[F] Completed p F where
  __ := Completion.mapRingEquiv (Closure.galois (p := p) σ).toRingEquiv
    (Closure.isometry_galois p F σ).continuous (Closure.isometry_galois p F σ⁻¹).continuous
  commutes' x := by
    change galoisRingHom p σ ((algebraMap F (Closure p F) x : Closure p F) : Completed p F) = _
    rw [galoisRingHom_coe, (Closure.galois (p := p) σ).commutes]
    rfl

@[simp]
theorem completedAutomorphism_apply (σ : Field.absoluteGaloisGroup F) (x : Completed p F) :
    completedAutomorphism p F σ x = galoisRingHom p σ x := rfl

/-- The completed automorphisms preserve distances. -/
theorem completedAutomorphism_isometry (σ : Field.absoluteGaloisGroup F) :
    Isometry (completedAutomorphism p F σ) :=
  Completion.isometry_mapRingHom (f := (Closure.galois (p := p) σ).toRingEquiv.toRingHom)
    (Closure.isometry_galois p F σ)

/-- The coefficient action in the group of isometric automorphisms used for
analytic scalar extension. -/
def galoisCoefficientAction : Field.absoluteGaloisGroup F →*
    isometricAutomorphisms F (Completed p F) where
  toFun σ := ⟨completedAutomorphism p F σ, fun x =>
    (completedAutomorphism_isometry p F σ).norm_map_of_map_zero (map_zero _) x⟩
  map_one' := by
    apply Subtype.ext
    ext x
    change galoisRingHom p 1 x = x
    rw [galoisRingHom_one]
    rfl
  map_mul' σ τ := by
    apply Subtype.ext
    ext x
    change galoisRingHom p (σ * τ) x = galoisRingHom p σ (galoisRingHom p τ x)
    rw [galoisRingHom_mul]
    rfl

/-- Each coefficient orbit is continuous for the Krull topology. An
algebraic approximation has an open stabilizer, and isometries preserve
the approximation error. -/
theorem continuous_galoisCoefficientOrbit (x : Completed p F) :
    Continuous fun σ : Field.absoluteGaloisGroup F => (galoisCoefficientAction p F σ).val x := by
  change Continuous fun σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F =>
    (galoisCoefficientAction p F σ).val x
  rw [continuous_iff_continuousAt]
  intro σ
  refine Metric.continuousAt_iff'.2 fun ε hε => ?_
  obtain ⟨a, ha⟩ := (Metric.denseRange_iff.mp Completion.denseRange_coe) x (ε / 2) (by positivity)
  let S := MulAction.stabilizer (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
    (show AlgebraicClosure F from a)
  have hS : IsOpen (S : Set (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)) :=
    stabilizer_isOpen_of_isIntegral (K := F) (show AlgebraicClosure F from a)
  have hnear : ∀ᶠ τ in 𝓝 σ, σ⁻¹ * τ ∈ S :=
    (hS.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [S])
  filter_upwards [hnear] with τ hτ
  have hfix : (σ⁻¹ * τ) (show AlgebraicClosure F from a) = a := hτ
  have hsame : Closure.galois (p := p) τ a = Closure.galois (p := p) σ a := by
    change σ.symm (τ (show AlgebraicClosure F from a)) = a at hfix
    change τ (show AlgebraicClosure F from a) = σ (show AlgebraicClosure F from a)
    simpa only [AlgEquiv.apply_symm_apply] using congrArg σ hfix
  let f := completedAutomorphism p F τ
  let g := completedAutomorphism p F σ
  have hfg : f (a : Completed p F) = g (a : Completed p F) := by
    exact (galoisRingHom_coe p τ a).trans
      ((congrArg (fun y : Closure p F => (y : Completed p F)) hsame).trans
        (galoisRingHom_coe p σ a).symm)
  change dist (f x) (g x) < ε
  calc
    dist (f x) (g x) ≤ dist (f x) (f a) + dist (f a) (g x) := dist_triangle _ _ _
    _ = dist x a + dist (a : Completed p F) x := by
      rw [(completedAutomorphism_isometry p F τ).dist_eq, hfg,
        (completedAutomorphism_isometry p F σ).dist_eq]
    _ < ε := by rw [dist_comm (a : Completed p F) x]; linarith

end Langlands.Analytic.CompletedGaloisCoefficientAction
