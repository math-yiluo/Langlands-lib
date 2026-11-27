import Langlands.GroupScheme.Quaternionic.QuaternionConjugation
import Langlands.GroupScheme.Quaternionic.ScalarQuadratic
import Langlands.LinearAlgebra.NumberFieldQuadraticRepresentation
import Mathlib.RingTheory.Flat.Equalizer

/-! # Local-to-global principle for reduced norms of intertwiners

For a central quaternion division algebra `D` over a number field `F`, elements `h g ∈ D` and
`μ ∈ F`, the elements `x` with `μ x h = g x` form an `F`-subspace on which the reduced norm is
an anisotropic quadratic form. If `μ` is the reduced norm of such an element over every
completion, the quadratic representation theorem gives such an element over `F`.
-/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open Langlands.CentralSimple

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000

section Intertwiner

variable {F D : Type u} [Field F] [Ring D] [Algebra F D]

/-- The `F`-linear map `x ↦ μ x h - g x` whose kernel consists of the intertwiners. -/
def intertwinerDefect (μ : F) (h g : D) : D →ₗ[F] D :=
  μ • LinearMap.mulRight F h - LinearMap.mulLeft F g

theorem intertwinerDefect_apply (μ : F) (h g x : D) :
    intertwinerDefect μ h g x = μ • (x * h) - g * x :=
  rfl

/-- The scalar extension of the defect map is the defect map of the extended elements. -/
theorem lTensor_intertwinerDefect (R : Type u) [CommRing R] [Algebra F R] (μ : F) (h g : D)
    (x : R ⊗[F] D) :
    TensorProduct.AlgebraTensorModule.lTensor R R (intertwinerDefect μ h g) x =
      μ • (x * (1 ⊗ₜ[F] h)) - (1 ⊗ₜ[F] g) * x := by
  rw [TensorProduct.AlgebraTensorModule.coe_lTensor]
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    rw [LinearMap.lTensor_tmul, intertwinerDefect_apply, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.tmul_sub,
      TensorProduct.tmul_smul]
  | add x y hx hy =>
    rw [_root_.map_add, hx, hy, add_mul, mul_add, smul_add]
    abel

/-- The conjugate-product quadratic form `x ↦ ℓ (x τ x)`. -/
def conjugateProductQuadratic (τ : FirstKindInvolution F D) (ℓ : D →ₗ[F] F) :
    QuadraticForm F D :=
  LinearMap.BilinMap.toQuadraticMap
    (((LinearMap.mul F D).compl₁₂ LinearMap.id τ.toLinearMap).compr₂ ℓ)

theorem conjugateProductQuadratic_apply (τ : FirstKindInvolution F D) (ℓ : D →ₗ[F] F) (x : D) :
    conjugateProductQuadratic τ ℓ x = ℓ (x * τ x) :=
  rfl

theorem conjugateProductQuadratic_comp_baseChange [Invertible (2 : F)]
    (τ : FirstKindInvolution F D) (ℓ : D →ₗ[F] F) (V : Submodule F D) (R : Type u) [Field R]
    [Algebra F R] :
    QuadraticForm.baseChange R ((conjugateProductQuadratic τ ℓ).comp V.subtype) =
      (conjugateProductQuadratic (τ.baseChange R) (baseChangeScalarFunctional ℓ R)).comp
        (V.subtype.baseChange R) := by
  apply _root_.baseChange_ext
  intro x
  simp only [QuadraticForm.baseChange_tmul, conjugateProductQuadratic_apply,
    QuadraticMap.comp_apply, LinearMap.baseChange_tmul, Submodule.subtype_apply,
    FirstKindInvolution.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    baseChangeScalarFunctional_tmul]

end Intertwiner

section NumberField

variable {F D : Type u} [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D]
  (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
  (hsym : Module.finrank F σ.symmetricSubspace = 3)

/-- The existence of an intertwiner of prescribed reduced norm over a field extension. -/
def HasIntertwinerOfNorm (μ : F) (h g : D) (R : Type u) [CommRing R] [Algebra F R] : Prop :=
  ∃ x : R ⊗[F] D, μ • (x * (1 ⊗ₜ[F] h)) = (1 ⊗ₜ[F] g) * x ∧
    reducedNorm F D R x = algebraMap F R μ

include σ hdim hsym in
/-- An intertwiner `x` with `μ x h = g x` of reduced norm `μ` exists over `F` as soon as one
exists over every completion. -/
theorem exists_intertwiner_of_local (μ : F) (h g : D)
    (hinf : ∀ w : Global.InfinitePlace F, HasIntertwinerOfNorm μ h g w.Completion)
    (hfin : ∀ v : Global.FinitePlace F,
      HasIntertwinerOfNorm μ h g (Global.FiniteCompletion F v)) :
    ∃ y : D, μ • (y * h) = g * y ∧ reducedNorm F D F (1 ⊗ₜ[F] y) = μ := by
  let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  set τ := σ.quaternionConjugation hdim hsym
  have hτ : ∀ x : D, x * τ x = algebraMap F D (reducedNorm F D F (1 ⊗ₜ[F] x)) :=
    σ.quaternionConjugation_norm hdim hsym
  obtain ⟨ℓ, hℓ⟩ := (Algebra.linearMap F D).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F D).injective)
  have hscalar (s : F) : ℓ (algebraMap F D s) = s := LinearMap.congr_fun hℓ s
  have h1 : ℓ (1 : D) = 1 := by simpa only [_root_.map_one] using hscalar 1
  let f := intertwinerDefect μ h g
  let V := LinearMap.ker f
  let Q : QuadraticForm F V := (conjugateProductQuadratic τ ℓ).comp V.subtype
  have hρ (x : V) : Q x = reducedNorm F D F (1 ⊗ₜ[F] (x : D)) := by
    change ℓ ((x : D) * τ x) = _
    rw [hτ, hscalar]
  have hzero (x : V) (hx : Q x = 0) : x = 0 := by
    have hp := hτ (x : D)
    rw [← hρ x, hx, _root_.map_zero] at hp
    apply Subtype.ext
    rcases mul_eq_zero.mp hp with h | h
    · exact h
    · exact τ.injective (h.trans τ.map_zero.symm)
  have hnd : Q.polarBilin.Nondegenerate := by
    apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    intro x hx
    apply hzero x
    have h := hx x
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul, ← two_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (two_ne_zero : (2 : F) ≠ 0)
  have localRep {R : Type u} [Field R] [Algebra F R] (hR : HasIntertwinerOfNorm μ h g R) :
      ∃ y, Q.baseChange R y = algebraMap F R μ := by
    obtain ⟨x, hx, ha⟩ := hR
    have hker : x ∈ LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor R R f) := by
      rw [LinearMap.mem_ker, lTensor_intertwinerDefect, hx, sub_self]
    rw [Module.Flat.ker_lTensor_eq] at hker
    obtain ⟨y, hy⟩ := hker
    refine ⟨y, ?_⟩
    have hy' : V.subtype.baseChange R y = x := by
      rw [LinearMap.baseChange_eq_lTensor, ← TensorProduct.AlgebraTensorModule.coe_lTensor (A := R)]
      exact hy
    change QuadraticForm.baseChange R ((conjugateProductQuadratic τ ℓ).comp V.subtype) y = _
    rw [conjugateProductQuadratic_comp_baseChange, QuadraticMap.comp_apply, hy',
      conjugateProductQuadratic_apply, σ.quaternionConjugation_norm_baseChange hdim hsym R x,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
      baseChangeScalarFunctional_tmul, h1, one_smul, ha]
  have hQloc (v : Global.Place F) : ∃ y, Q.baseChange (Global.placeCompletion F v) y =
      algebraMap F (Global.placeCompletion F v) μ := by
    rcases v with v | v
    · exact localRep (R := v.Completion) (hinf v)
    · exact localRep (R := Global.FiniteCompletion F v) (hfin v)
  obtain ⟨x, hx⟩ := Langlands.numberFieldQuadraticRepresentation F V Q μ hnd hQloc
  refine ⟨x, ?_, (hρ x).symm.trans hx⟩
  have hmem : f x = 0 := x.property
  rw [intertwinerDefect_apply, sub_eq_zero] at hmem
  exact hmem

end NumberField

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
