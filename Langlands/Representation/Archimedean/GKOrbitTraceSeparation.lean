import Langlands.Representation.Archimedean.GKCompressedTrace
import Langlands.Representation.Archimedean.SmoothHilbert
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.LinearAlgebra.StdBasis

/-! # Group coefficient trace tests for algebraic archimedean modules -/

noncomputable section

open scoped Manifold ContDiff TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type) [RCLike F] (n : ℕ)

local notation "GL" => Langlands.GeneralLinear n F
local notation "K" => Matrix.unitaryGroup (Fin n) F
local notation "Mat" => Matrix (Fin n) (Fin n) F
local notation "𝔤" => ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) F
local notation "I" => matrixModel F n

section OneAction

variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [AddCommGroup V] [Module ℂ V] (R : Langlands.GeneralLinear n F →* (H →L[ℂ] H))
  (e : V →ₗ[ℂ] DerivativeSmoothVectors (matrixModel F n) R) {d : ℕ} (ℓ : Fin d → StrongDual ℂ H)

local notation "ε" => DerivativeSmoothVectors.derivativeCLM I R []

/-- A finite sum of actual orbit coefficients, linear in the family of algebraic input vectors. -/
def orbitCoefficientProfile : (Fin d → V) →ₗ[ℂ] (GL → ℂ) :=
  LinearMap.pi fun g => ∑ i : Fin d,
    (((ℓ i).comp (R g)).comp ε).toLinearMap.comp (e.comp (LinearMap.proj i))

@[simp]
theorem orbitCoefficientProfile_apply (v : Fin d → V) (g : GL) :
    orbitCoefficientProfile F n R e ℓ v g = ∑ i, ℓ i (R g (ε (e (v i)))) := by
  simp only [orbitCoefficientProfile, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.coe_comp, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    Function.comp_apply, LinearMap.proj_apply]

private theorem orbitCoefficientProfile_compact (ρ : Representation ℂ K V)
    (hk : ∀ (k : K) (v : V), e (ρ k v) =
      DerivativeSmoothVectors.representation I R (Unitary.toUnits k) (e v))
    (k : K) (v : Fin d → V) (g : GL) :
    orbitCoefficientProfile F n R e ℓ (fun i => ρ k (v i)) g =
      orbitCoefficientProfile F n R e ℓ v (g * Unitary.toUnits k) := by
  simp only [orbitCoefficientProfile_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hk, map_mul, mul_apply_eq_comp]
  rfl

private theorem hasDerivAt_orbitCoefficientProfile_exp
    (π : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hX : ∀ (X : Mat) (v : V), e (π (1 ⊗ₜ[ℝ] X) v) = DerivativeSmoothVectors.operator I R X (e v))
    (hExp : HasSmoothHilbertExponentialDerivatives F n R)
    (X : Mat) (v : Fin d → V) (g : GL) :
    HasDerivAt (fun t : ℝ => orbitCoefficientProfile F n R e ℓ v (g * generalLinearRealExp F n X t))
      (orbitCoefficientProfile F n R e ℓ (fun i => π (1 ⊗ₜ[ℝ] X) (v i)) g) 0 := by
  simp only [orbitCoefficientProfile_apply]
  refine HasDerivAt.fun_sum (u := Finset.univ) fun i _ => ?_
  rw [hX]
  have hempty (a : GL) :
      ε (DerivativeSmoothVectors.representation I R a (e (v i))) = R a (ε (e (v i))) := rfl
  simpa only [map_mul, mul_apply_eq_comp, ContinuousLinearMap.comp_apply, hempty] using!
    hExp X (e (v i)) (((ℓ i).comp (R g)).comp ε)

private theorem compressedTrace_profile (v : Fin d → V) (T : Module.End ℂ V) :
    Langlands.CharacterSeparation.compressedTrace
      ((Pi.basisFun ℂ (Fin d)).constr ℂ v)
      (LinearMap.pi fun i => (ℓ i).toLinearMap.comp ((ε).toLinearMap.comp e)) T =
      orbitCoefficientProfile F n R e ℓ (fun i => T (v i)) 1 := by
  rw [Langlands.CharacterSeparation.compressedTrace,
    LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin d)), Matrix.trace, orbitCoefficientProfile_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr, LinearMap.comp_apply,
    LinearMap.pi_apply, Module.Basis.constr_basis, ContinuousLinearMap.coe_coe,
    map_one, one_apply_eq_self]

end OneAction

section Compare

variable {H J V W : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  (R : Langlands.GeneralLinear n F →* (H →L[ℂ] H))
  (S : Langlands.GeneralLinear n F →* (J →L[ℂ] J))
  (e : V →ₗ[ℂ] DerivativeSmoothVectors (matrixModel F n) R)
  (f : W →ₗ[ℂ] DerivativeSmoothVectors (matrixModel F n) S)
  (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) F) V)
  (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) F) →ₗ⁅ℂ⁆ Module.End ℂ V)
  (σ : Representation ℂ (Matrix.unitaryGroup (Fin n) F) W)
  (τ : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) F) →ₗ⁅ℂ⁆ Module.End ℂ W)
  {d b : ℕ} (ℓ : Fin d → StrongDual ℂ H) (m : Fin b → StrongDual ℂ J)

local notation "𝒞" => orbitCoefficientProfile F n R e ℓ
local notation "𝒟" => orbitCoefficientProfile F n S f m

private theorem orbitCoefficientProfile_freeAlgebra
    (hkR : ∀ (k : K) (v : V), e (ρ k v) =
      DerivativeSmoothVectors.representation I R (Unitary.toUnits k) (e v))
    (hkS : ∀ (k : K) (w : W), f (σ k w) =
      DerivativeSmoothVectors.representation I S (Unitary.toUnits k) (f w))
    (hXR : ∀ (X : Mat) (v : V), e (π (1 ⊗ₜ[ℝ] X) v) = DerivativeSmoothVectors.operator I R X (e v))
    (hXS : ∀ (X : Mat) (w : W), f (τ (1 ⊗ₜ[ℝ] X) w) = DerivativeSmoothVectors.operator I S X (f w))
    (hExpR : HasSmoothHilbertExponentialDerivatives F n R)
    (hExpS : HasSmoothHilbertExponentialDerivatives F n S)
    (a : FreeAlgebra ℂ (K ⊕ 𝔤)) : ∀ (v : Fin d → V) (w : Fin b → W),
      𝒞 v = 𝒟 w → 𝒞 (fun i => FreeAlgebra.lift ℂ (GKModuleDensity.gens ρ π) a (v i)) =
        𝒟 (fun i => FreeAlgebra.lift ℂ (GKModuleDensity.gens σ τ) a (w i)) := by
  induction a using FreeAlgebra.induction with
  | grade0 z =>
      intro v w hw
      simp only [AlgHom.commutes, Module.algebraMap_end_apply]
      change 𝒞 (z • v) = 𝒟 (z • w)
      rw [map_smul, map_smul, hw]
  | grade1 x =>
      simp only [FreeAlgebra.lift_ι_apply, GKModuleDensity.gens]
      cases x with
      | inl k =>
          intro v w hw
          change 𝒞 (fun i => ρ k (v i)) = 𝒟 (fun i => σ k (w i))
          ext g
          rw [orbitCoefficientProfile_compact F n R e ℓ ρ hkR,
            orbitCoefficientProfile_compact F n S f m σ hkS, hw]
      | inr X =>
          intro v w hw
          change 𝒞 (fun i => π X (v i)) = 𝒟 (fun i => τ X (w i))
          induction X using TensorProduct.inductionOn with
          | tmul z X =>
              have hz : z ⊗ₜ[ℝ] X = z • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
                rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
              simp only [hz, map_smul, LinearMap.smul_apply]
              change 𝒞 (z • (fun i => π (1 ⊗ₜ[ℝ] X) (v i))) =
                𝒟 (z • (fun i => τ (1 ⊗ₜ[ℝ] X) (w i)))
              rw [map_smul, map_smul]
              congr 1
              ext g
              have hr := hasDerivAt_orbitCoefficientProfile_exp F n R e ℓ π hXR hExpR X v g
              rw [hw] at hr
              exact hr.unique (hasDerivAt_orbitCoefficientProfile_exp F n S f m τ hXS hExpS X w g)
          | add X Y hX hY =>
              simp only [map_add, LinearMap.add_apply]
              change 𝒞 ((fun i => π X (v i)) + (fun i => π Y (v i))) =
                𝒟 ((fun i => τ X (w i)) + (fun i => τ Y (w i)))
              rw [map_add, map_add, hX, hY]
  | mul a₁ a₂ ih₁ ih₂ =>
      intro v w hw
      simp only [map_mul, Module.End.mul_apply]
      exact ih₁ _ _ (ih₂ _ _ hw)
  | add a₁ a₂ ih₁ ih₂ =>
      intro v w hw
      simp only [map_add, LinearMap.add_apply]
      change 𝒞 ((fun i => FreeAlgebra.lift ℂ (GKModuleDensity.gens ρ π) a₁ (v i)) +
        (fun i => FreeAlgebra.lift ℂ (GKModuleDensity.gens ρ π) a₂ (v i))) =
        𝒟 ((fun i => FreeAlgebra.lift ℂ (GKModuleDensity.gens σ τ) a₁ (w i)) +
          (fun i => FreeAlgebra.lift ℂ (GKModuleDensity.gens σ τ) a₂ (w i)))
      rw [map_add, map_add, ih₁ _ _ hw, ih₂ _ _ hw]

/-- Equal finite sums of group orbit coefficients give equivalent irreducible algebraic
modules if the sums have nonzero value at the identity and the embeddings compare
compact and derived operators with the genuine smooth actions. -/
theorem exists_gkEquiv_of_orbitCoefficientProfile_eq
    (hirrR : IsIrreducibleGKModule ρ π) (hirrS : IsIrreducibleGKModule σ τ)
    (hkR : ∀ (k : K) (v : V), e (ρ k v) =
      DerivativeSmoothVectors.representation I R (Unitary.toUnits k) (e v))
    (hkS : ∀ (k : K) (w : W), f (σ k w) =
      DerivativeSmoothVectors.representation I S (Unitary.toUnits k) (f w))
    (hXR : ∀ (X : Mat) (v : V), e (π (1 ⊗ₜ[ℝ] X) v) = DerivativeSmoothVectors.operator I R X (e v))
    (hXS : ∀ (X : Mat) (w : W), f (τ (1 ⊗ₜ[ℝ] X) w) = DerivativeSmoothVectors.operator I S X (f w))
    (hExpR : HasSmoothHilbertExponentialDerivatives F n R)
    (hExpS : HasSmoothHilbertExponentialDerivatives F n S)
    (v : Fin d → V) (w : Fin b → W) (hv : 𝒞 v 1 ≠ 0) (h : 𝒞 v = 𝒟 w) :
    ∃ a : V ≃ₗ[ℂ] W, (∀ (k : K) (v : V), a (ρ k v) = σ k (a v)) ∧
      ∀ (X : 𝔤) (v : V), a (π X v) = τ X (a v) := by
  let e₀ := DerivativeSmoothVectors.derivativeCLM I R []
  let f₀ := DerivativeSmoothVectors.derivativeCLM I S []
  refine GKModuleDensity.exists_gkEquiv_of_compressedTrace_eq ρ π σ τ hirrR hirrS
    ((Pi.basisFun ℂ (Fin d)).constr ℂ v)
    (LinearMap.pi fun i => (ℓ i).toLinearMap.comp (e₀.toLinearMap.comp e))
    ((Pi.basisFun ℂ (Fin b)).constr ℂ w)
    (LinearMap.pi fun i => (m i).toLinearMap.comp (f₀.toLinearMap.comp f)) ?_ ?_
  · rw [compressedTrace_profile]
    exact hv
  · intro a
    rw [compressedTrace_profile, compressedTrace_profile]
    exact congrFun
      (orbitCoefficientProfile_freeAlgebra F n R S e f ρ π σ τ ℓ m hkR hkS hXR hXS hExpR hExpS a v w h) 1

end Compare

end Langlands.Archimedean
