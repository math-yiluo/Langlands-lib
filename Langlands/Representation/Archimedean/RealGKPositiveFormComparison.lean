import Langlands.Representation.Archimedean.RealGKFiniteHermitianDual
import Langlands.Representation.Archimedean.GKModuleDensity
import Langlands.Representation.Archimedean.RealStandardModuleAdmissible

/-! # Comparison with a positive invariant real `(𝔤, K)`-form -/

noncomputable section

open scoped ComplexConjugate TensorProduct Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.KFiniteDual Langlands.LocalFactor.Archimedean RealContragredient

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

/-- Invariant sesquilinear forms on an irreducible admissible real `(𝔤, K)`-module
are scalar multiples of a positive invariant form when one is given. -/
def RealGKPositiveFormComparisonStatement : Prop :=
  ∀ {n : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsRealGKModule n ρ π → GKModuleDensity.Hyp ρ π →
    ∀ (b : InvariantPositiveForm ρ) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ),
      (∀ (X : Matrix (Fin n) (Fin n) ℝ) v w,
        b.inner (π (1 ⊗ₜ X) v) w + b.inner v (π (1 ⊗ₜ X) w) = 0) →
      (∀ k v w, B (ρ k v) (ρ k w) = B v w) →
      (∀ (X : Matrix (Fin n) (Fin n) ℝ) v w,
        B (π (1 ⊗ₜ X) v) w + B v (π (1 ⊗ₜ X) w) = 0) →
      ∃ c : ℂ, ∀ v w, B v w = c * b.inner v w

theorem realGKPositiveFormComparison : RealGKPositiveFormComparisonStatement.{u} := by
  intro n V _ _ ρ π hgk hDensity b B hb hBK hBL
  have hBdual (k : Matrix.unitaryGroup (Fin n) ℝ) (v : V) :
      B (ρ k v) = ρ.dual k (B v) := by
    ext w
    change B (ρ k v) w = B v (ρ k⁻¹ w)
    have h := hBK k v (ρ k⁻¹ w)
    simpa only [Representation.self_inv_apply] using h
  let T : V →ₗ⋆[ℂ] kDual ρ := B.codRestrict (kDual ρ) fun v =>
    (hgk.1 v).map_conjugateLinear B hBdual
  have hTK (k : Matrix.unitaryGroup (Fin n) ℝ) (v : V) :
      T (ρ k v) = kDualRep ρ k (T v) := Subtype.ext (hBdual k v)
  have hTL (X : Matrix (Fin n) (Fin n) ℝ) (v : V) :
      T (π (1 ⊗ₜ X) v) = dualLie hgk (1 ⊗ₜ X) (T v) := by
    apply Subtype.ext
    ext w
    rw [dualLie_apply_apply]
    exact eq_neg_of_add_eq_zero_left (hBL X v w)
  let U := LinearEquiv.ofBijective (b.toKFiniteDual hgk.1)
    ⟨b.toKFiniteDual_injective hgk.1,
      realGK_toKFiniteDual_surjective hgk b hb hDensity.irreducible hDensity.admissible⟩
  let A : Module.End ℂ V := U.symm.toLinearMap.comp T
  have hAU (v : V) : b.toKFiniteDual hgk.1 (A v) = T v :=
    U.apply_symm_apply (T v)
  have hAK (k : Matrix.unitaryGroup (Fin n) ℝ) (v : V) :
      A (ρ k v) = ρ k (A v) := by
    apply b.toKFiniteDual_injective hgk.1
    rw [hAU, hTK, b.toKFiniteDual_compact, hAU]
  have hALreal (X : Matrix (Fin n) (Fin n) ℝ) (v : V) :
      A (π (1 ⊗ₜ X) v) = π (1 ⊗ₜ X) (A v) := by
    apply b.toKFiniteDual_injective hgk.1
    rw [hAU, hTL, realGK_toKFiniteDual_lie hgk b hb, hAU]
  have hAL (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) (v : V) :
      A (π X v) = π X (A v) := by
    induction X using TensorProduct.inductionOn with
    | tmul c Y =>
      have hc : c ⊗ₜ[ℝ] Y = c • ((1 : ℂ) ⊗ₜ[ℝ] Y) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hc, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, hALreal]
    | add X Y hX hY =>
      simp only [map_add, LinearMap.add_apply, hX, hY]
  obtain ⟨c, hc⟩ := GKModuleDensity.exists_eq_scalar hDensity A hAK hAL
  refine ⟨conj c, fun v w => ?_⟩
  have hp := congrArg (fun ℓ : kDual ρ => (ℓ : Module.Dual ℂ V) w) (hAU v)
  change b.inner (A v) w = B v w at hp
  rw [hc v, b.smul_left] at hp
  exact hp.symm

/-- An irreducible standard module satisfies the hypotheses of the compact
Schur lemma. -/
theorem realStandardDensityHyp {n : ℕ} {ds : List RealBlock}
    (hirr : IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds)) :
    GKModuleDensity.Hyp (realStandardRep n ds) (realStandardLie n ds) where
  irreducible := hirr
  admissible := realStandardAdmissible n ds
  finite f := ⟨FiniteVectors.orbitSpan (realStandardRep n ds) f,
    FiniteVectors.self_mem_orbitSpan _ f, (isRealGKModule_realStandardModule n ds).1 f,
    fun k _ hv => (FiniteVectors.orbitSubrepresentation _ f).apply_mem_toSubmodule k hv⟩
  continuous f ℓ := kFiniteRep_continuous (realStandardModule n ds)
    (fun _ hf => hf.1.1) (fun k _ _ hf => rightTranslation_mem_realStandardModule_of_mem hf k) f ℓ

end Langlands.Archimedean
