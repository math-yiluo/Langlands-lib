import Langlands.Representation.Shahidi.Characters
import Langlands.HarmonicAnalysis.StableIntegral
import Mathlib.Analysis.Matrix.MeasurableSpace

/-! # Concrete scalar Jacquet integrands and their stabilization domains -/

noncomputable section

namespace Langlands.Shahidi

open HarmonicAnalysis MeasureTheory

universe uF uV

variable {F : Type uF} [Field F] [TopologicalSpace F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (m n : ℕ) (ψ : UnitaryAdditiveCharacter F) (ℓ : V →ₗ[ℂ] ℂ)

/-- The scalar integrand of the original Jacquet functional, in the actual
exchanged-radical coordinates of equation (0.2). -/
def jacquetIntegrand :
    (GeneralLinear (m + 1 + (n + 1)) F → V) →ₗ[ℂ]
      (Matrix (Fin (n + 1)) (Fin (m + 1)) F → ℂ) where
  toFun f a := intertwiningJacquetKernel m n ψ a *
    ℓ (f (blockWeyl (m + 1) (n + 1) F *
      intertwiningUnipotent (m + 1) (n + 1) F a))
  map_add' f g := by ext a; simp [mul_add]
  map_smul' c f := by ext a; simp [mul_left_comm]

@[simp] theorem jacquetIntegrand_apply
    (f : GeneralLinear (m + 1 + (n + 1)) F → V)
    (a : Matrix (Fin (n + 1)) (Fin (m + 1)) F) :
    jacquetIntegrand m n ψ ℓ f a = intertwiningJacquetKernel m n ψ a *
      ℓ (f (blockWeyl (m + 1) (n + 1) F *
        intertwiningUnipotent (m + 1) (n + 1) F a)) := rfl

/-- The scalar integrand for the swapped functional: the original radical,
the inverse Weyl element, and the original-radical conjugate character. -/
def swappedJacquetIntegrand :
    (GeneralLinear (m + 1 + (n + 1)) F → V) →ₗ[ℂ]
      (Matrix (Fin (m + 1)) (Fin (n + 1)) F → ℂ) where
  toFun f a := upperJacquetKernel m n ψ a *
    ℓ (f ((blockWeyl (m + 1) (n + 1) F)⁻¹ * upper (m + 1) (n + 1) F a))
  map_add' f g := by ext a; simp [mul_add]
  map_smul' c f := by ext a; simp [mul_left_comm]

@[simp] theorem swappedJacquetIntegrand_apply
    (f : GeneralLinear (m + 1 + (n + 1)) F → V)
    (a : Matrix (Fin (m + 1)) (Fin (n + 1)) F) :
    swappedJacquetIntegrand m n ψ ℓ f a = upperJacquetKernel m n ψ a *
      ℓ (f ((blockWeyl (m + 1) (n + 1) F)⁻¹ * upper (m + 1) (n + 1) F a)) := rfl

/-- In the lower-radical coordinates of page 78, the same integrand evaluates
the right translate of the original function at the actual lower matrix. -/
theorem jacquetIntegrand_lower
    (f : GeneralLinear (m + 1 + (n + 1)) F → V)
    (a : Matrix (Fin (n + 1)) (Fin (m + 1)) F) :
    jacquetIntegrand m n ψ ℓ f a = intertwiningJacquetKernel m n ψ a *
      ℓ (f (lower (m + 1) (n + 1) F a * blockWeyl (m + 1) (n + 1) F)) := by
  simp only [jacquetIntegrand_apply, lower, mul_assoc, inv_mul_cancel, mul_one]

/-- The right translation by the inverse Weyl matrix used on source page 78
turns the original integrand into direct evaluation on the lower radical. -/
theorem jacquetIntegrand_rightTranslate_inv
    (f : GeneralLinear (m + 1 + (n + 1)) F → V)
    (a : Matrix (Fin (n + 1)) (Fin (m + 1)) F) :
    jacquetIntegrand m n ψ ℓ
        (fun g => f (g * (blockWeyl (m + 1) (n + 1) F)⁻¹)) a =
      intertwiningJacquetKernel m n ψ a * ℓ (f (lower (m + 1) (n + 1) F a)) := rfl

variable [IsTopologicalRing F] [MeasurableSpace F]

/-- The original scalar Jacquet integral stabilizes to `z`, including actual
integrability on every sufficiently large compact open truncation. -/
def HasJacquetIntegral
    (μ : Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F))
    (f : GeneralLinear (m + 1 + (n + 1)) F → V) (z : ℂ) : Prop :=
  HasStableIntegral μ (jacquetIntegrand m n ψ ℓ f) z

/-- The analogous stabilization relation for the swapped functional. -/
def HasSwappedJacquetIntegral
    (μ : Measure (Matrix (Fin (m + 1)) (Fin (n + 1)) F))
    (f : GeneralLinear (m + 1 + (n + 1)) F → V) (z : ℂ) : Prop :=
  HasStableIntegral μ (swappedJacquetIntegrand m n ψ ℓ f) z

theorem HasJacquetIntegral.unique
    {μ : Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F)}
    {f : GeneralLinear (m + 1 + (n + 1)) F → V} {z w : ℂ}
    (hz : HasJacquetIntegral m n ψ ℓ μ f z)
    (hw : HasJacquetIntegral m n ψ ℓ μ f w) : z = w :=
  HasStableIntegral.unique hz hw

theorem HasSwappedJacquetIntegral.unique
    {μ : Measure (Matrix (Fin (m + 1)) (Fin (n + 1)) F)}
    {f : GeneralLinear (m + 1 + (n + 1)) F → V} {z w : ℂ}
    (hz : HasSwappedJacquetIntegral m n ψ ℓ μ f z)
    (hw : HasSwappedJacquetIntegral m n ψ ℓ μ f w) : z = w :=
  HasStableIntegral.unique hz hw

/-- Pull back the actual stable-integrability submodule along the original
scalar integrand map. -/
def jacquetStableDomain
    (μ : Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F))
    (h : ∃ K : OpenAddSubgroup (Matrix (Fin (n + 1)) (Fin (m + 1)) F),
      IsCompact (K : Set (Matrix (Fin (n + 1)) (Fin (m + 1)) F))) :
    Submodule ℂ (GeneralLinear (m + 1 + (n + 1)) F → V) :=
  (stableIntegrableSubmodule μ h).comap (jacquetIntegrand m n ψ ℓ)

/-- The swapped domain uses its own rectangular coordinate space and measure. -/
def swappedJacquetStableDomain
    (μ : Measure (Matrix (Fin (m + 1)) (Fin (n + 1)) F))
    (h : ∃ K : OpenAddSubgroup (Matrix (Fin (m + 1)) (Fin (n + 1)) F),
      IsCompact (K : Set (Matrix (Fin (m + 1)) (Fin (n + 1)) F))) :
    Submodule ℂ (GeneralLinear (m + 1 + (n + 1)) F → V) :=
  (stableIntegrableSubmodule μ h).comap (swappedJacquetIntegrand m n ψ ℓ)

@[simp] theorem mem_jacquetStableDomain
    (μ : Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F))
    (h : ∃ K : OpenAddSubgroup (Matrix (Fin (n + 1)) (Fin (m + 1)) F),
      IsCompact (K : Set (Matrix (Fin (n + 1)) (Fin (m + 1)) F)))
    (f : GeneralLinear (m + 1 + (n + 1)) F → V) :
    f ∈ jacquetStableDomain m n ψ ℓ μ h ↔
      ∃ z, HasJacquetIntegral m n ψ ℓ μ f z := Iff.rfl

@[simp] theorem mem_swappedJacquetStableDomain
    (μ : Measure (Matrix (Fin (m + 1)) (Fin (n + 1)) F))
    (h : ∃ K : OpenAddSubgroup (Matrix (Fin (m + 1)) (Fin (n + 1)) F),
      IsCompact (K : Set (Matrix (Fin (m + 1)) (Fin (n + 1)) F)))
    (f : GeneralLinear (m + 1 + (n + 1)) F → V) :
    f ∈ swappedJacquetStableDomain m n ψ ℓ μ h ↔
      ∃ z, HasSwappedJacquetIntegral m n ψ ℓ μ f z := Iff.rfl

/-- The stabilized original scalar functional, only on its proved domain. -/
def jacquetStableFunctional
    (μ : Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F))
    (h : ∃ K : OpenAddSubgroup (Matrix (Fin (n + 1)) (Fin (m + 1)) F),
      IsCompact (K : Set (Matrix (Fin (n + 1)) (Fin (m + 1)) F))) :
    jacquetStableDomain m n ψ ℓ μ h →ₗ[ℂ] ℂ :=
  (stableIntegral μ h).comp
    (LinearMap.codRestrict (stableIntegrableSubmodule μ h)
      ((jacquetIntegrand m n ψ ℓ).comp (jacquetStableDomain m n ψ ℓ μ h).subtype)
      (fun f => f.property))

/-- The stabilized swapped scalar functional, only on its proved domain. -/
def swappedJacquetStableFunctional
    (μ : Measure (Matrix (Fin (m + 1)) (Fin (n + 1)) F))
    (h : ∃ K : OpenAddSubgroup (Matrix (Fin (m + 1)) (Fin (n + 1)) F),
      IsCompact (K : Set (Matrix (Fin (m + 1)) (Fin (n + 1)) F))) :
    swappedJacquetStableDomain m n ψ ℓ μ h →ₗ[ℂ] ℂ :=
  (stableIntegral μ h).comp
    (LinearMap.codRestrict (stableIntegrableSubmodule μ h)
      ((swappedJacquetIntegrand m n ψ ℓ).comp
        (swappedJacquetStableDomain m n ψ ℓ μ h).subtype)
      (fun f => f.property))

theorem hasJacquetIntegral_jacquetStableFunctional
    (μ : Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F))
    (h : ∃ K : OpenAddSubgroup (Matrix (Fin (n + 1)) (Fin (m + 1)) F),
      IsCompact (K : Set (Matrix (Fin (n + 1)) (Fin (m + 1)) F)))
    (f : jacquetStableDomain m n ψ ℓ μ h) :
    HasJacquetIntegral m n ψ ℓ μ f.val (jacquetStableFunctional m n ψ ℓ μ h f) :=
  hasStableIntegral_stableIntegral h ⟨jacquetIntegrand m n ψ ℓ f.val, f.property⟩

theorem hasSwappedJacquetIntegral_swappedJacquetStableFunctional
    (μ : Measure (Matrix (Fin (m + 1)) (Fin (n + 1)) F))
    (h : ∃ K : OpenAddSubgroup (Matrix (Fin (m + 1)) (Fin (n + 1)) F),
      IsCompact (K : Set (Matrix (Fin (m + 1)) (Fin (n + 1)) F)))
    (f : swappedJacquetStableDomain m n ψ ℓ μ h) :
    HasSwappedJacquetIntegral m n ψ ℓ μ f.val
      (swappedJacquetStableFunctional m n ψ ℓ μ h f) :=
  hasStableIntegral_stableIntegral h ⟨swappedJacquetIntegrand m n ψ ℓ f.val, f.property⟩

theorem jacquetStableFunctional_eq
    (μ : Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F))
    (h : ∃ K : OpenAddSubgroup (Matrix (Fin (n + 1)) (Fin (m + 1)) F),
      IsCompact (K : Set (Matrix (Fin (n + 1)) (Fin (m + 1)) F)))
    (f : jacquetStableDomain m n ψ ℓ μ h) {z : ℂ}
    (hz : HasJacquetIntegral m n ψ ℓ μ f.val z) :
    jacquetStableFunctional m n ψ ℓ μ h f = z :=
  HasStableIntegral.unique (hasJacquetIntegral_jacquetStableFunctional m n ψ ℓ μ h f) hz

theorem swappedJacquetStableFunctional_eq
    (μ : Measure (Matrix (Fin (m + 1)) (Fin (n + 1)) F))
    (h : ∃ K : OpenAddSubgroup (Matrix (Fin (m + 1)) (Fin (n + 1)) F),
      IsCompact (K : Set (Matrix (Fin (m + 1)) (Fin (n + 1)) F)))
    (f : swappedJacquetStableDomain m n ψ ℓ μ h) {z : ℂ}
    (hz : HasSwappedJacquetIntegral m n ψ ℓ μ f.val z) :
    swappedJacquetStableFunctional m n ψ ℓ μ h f = z :=
  HasStableIntegral.unique
    (hasSwappedJacquetIntegral_swappedJacquetStableFunctional m n ψ ℓ μ h f) hz

end Langlands.Shahidi
