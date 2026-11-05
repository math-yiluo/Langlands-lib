import Langlands.Representation.Plancherel.CoefficientTensors
import Langlands.Representation.Unitary.PositiveFormTensor
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SquareIntegrableSemisimplicity

/-!
# Positive forms on actual coefficient tensors and inverse dual scaling

The existing Hermitian identification and smooth-dual form are reused.
Positive scaling of the original form scales its actual dual by the reciprocal,
so their tensor form is unchanged.
-/

noncomputable section

open scoped TensorProduct ComplexConjugate

namespace Langlands

universe uG uV

namespace InvariantPositiveForm

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/-- Positive rescaling multiplies each actual linear functional by that scalar. -/
theorem rightFunctional_rescale (b : InvariantPositiveForm ρ)
    (a : ℝ) (ha : 0 < a) (v : V) :
    (b.rescale a ha).rightFunctional v = (a : ℂ) • b.rightFunctional v := by
  apply LinearMap.ext
  intro w
  rfl

variable [TopologicalSpace G]

/-- The actual conjugate-linear map to the smooth dual scales by the same real
scalar as the form. -/
theorem toSmoothDual_rescale (b : InvariantPositiveForm ρ)
    (hρ : IsSmooth ρ) (a : ℝ) (ha : 0 < a) (v : V) :
    (b.rescale a ha).toSmoothDual hρ v = (a : ℂ) • b.toSmoothDual hρ v :=
  Subtype.ext (b.rightFunctional_rescale a ha v)

variable [IsTopologicalGroup G]

variable (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
  IsCompact (L : Set G) ∧ L ≤ K) (hρ : IsAdmissible ρ)

/-- The chosen Hermitian equivalences have the same pointwise scaling law as
the maps from which they are built. -/
theorem smoothDualEquiv_rescale (b : InvariantPositiveForm ρ)
    (a : ℝ) (ha : 0 < a) (v : V) :
    (b.rescale a ha).smoothDualEquiv hcof hρ v =
      (a : ℂ) • b.smoothDualEquiv hcof hρ v :=
  b.toSmoothDual_rescale hρ.1 a ha v

/-- Inverting the actual Hermitian equivalence changes the positive real
scaling factor to its reciprocal. -/
theorem smoothDualEquiv_rescale_symm (b : InvariantPositiveForm ρ)
    (a : ℝ) (ha : 0 < a) (ℓ : SmoothDual ρ) :
    ((b.rescale a ha).smoothDualEquiv hcof hρ).symm ℓ =
      (a⁻¹ : ℝ) • (b.smoothDualEquiv hcof hρ).symm ℓ := by
  apply ((b.rescale a ha).smoothDualEquiv hcof hρ).injective
  rw [LinearEquiv.apply_symm_apply, smoothDualEquiv_rescale]
  change ℓ = (a : ℂ) • b.smoothDualEquiv hcof hρ
    (((a⁻¹ : ℝ) : ℂ) • (b.smoothDualEquiv hcof hρ).symm ℓ)
  rw [LinearEquiv.map_smulₛₗ, Complex.conj_ofReal,
    LinearEquiv.apply_symm_apply, smul_smul, ← Complex.ofReal_mul,
    mul_inv_cancel₀ ha.ne', Complex.ofReal_one, one_smul]

end InvariantPositiveForm

namespace HarishChandraSchwartz

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
    IsCompact (L : Set G) ∧ L ≤ K) (hρ : IsAdmissible ρ)

/-- The existing positive form on the actual smooth contragredient scales by
the reciprocal of the scaling on the original representation. -/
theorem dualInvariantForm_rescale (b : InvariantPositiveForm ρ)
    (a : ℝ) (ha : 0 < a) :
    dualInvariantForm (b.rescale a ha) hcof hρ =
      (dualInvariantForm b hcof hρ).rescale a⁻¹ (inv_pos.mpr ha) := by
  apply InvariantPositiveForm.ext_inner
  intro ℓ m
  change (a : ℂ) * b.inner
      (((b.rescale a ha).smoothDualEquiv hcof hρ).symm m)
      (((b.rescale a ha).smoothDualEquiv hcof hρ).symm ℓ) =
    ((a⁻¹ : ℝ) : ℂ) * b.inner
      ((b.smoothDualEquiv hcof hρ).symm m)
      ((b.smoothDualEquiv hcof hρ).symm ℓ)
  rw [b.smoothDualEquiv_rescale_symm hcof hρ a ha m,
    b.smoothDualEquiv_rescale_symm hcof hρ a ha ℓ]
  change (a : ℂ) * b.inner
      (((a⁻¹ : ℝ) : ℂ) • (b.smoothDualEquiv hcof hρ).symm m)
      (((a⁻¹ : ℝ) : ℂ) • (b.smoothDualEquiv hcof hρ).symm ℓ) = _
  rw [b.smul_left, Complex.conj_ofReal]
  change (a : ℂ) * (((a⁻¹ : ℝ) : ℂ) *
      b.rightFunctional ((b.smoothDualEquiv hcof hρ).symm m)
        (((a⁻¹ : ℝ) : ℂ) • (b.smoothDualEquiv hcof hρ).symm ℓ)) = _
  rw [map_smul, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ ha.ne', Complex.ofReal_one, one_mul]
  rfl

end HarishChandraSchwartz

namespace Plancherel

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : SmoothRep.{0, uG, uV} ℂ G)
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
    IsCompact (L : Set G) ∧ L ≤ K)
  (hA : IsAdmissible A.representation)

/-- The positive invariant form on a canonical coefficient tensor, using the
actual smooth-dual form of the chosen original form. -/
def coefficientTensorInvariantForm (b : InvariantPositiveForm A.representation) :
    InvariantPositiveForm (coefficientTensorAction A) :=
  b.tensorProduct (HarishChandraSchwartz.dualInvariantForm b hcof hA)

@[simp]
theorem coefficientTensorInvariantForm_inner_tmul
    (b : InvariantPositiveForm A.representation)
    (v w : A) (ℓ m : SmoothDual A.representation) :
    (coefficientTensorInvariantForm A hcof hA b).inner
      (v ⊗ₜ[ℂ] ℓ) (w ⊗ₜ[ℂ] m) =
        b.inner v w *
          (HarishChandraSchwartz.dualInvariantForm b hcof hA).inner ℓ m :=
  b.tensorProduct_inner_tmul _ v w ℓ m

/-- Positive rescaling of the original form leaves the entire actual
coefficient-tensor form unchanged. -/
theorem coefficientTensorInvariantForm_rescale
    (b : InvariantPositiveForm A.representation) (a : ℝ) (ha : 0 < a) :
    coefficientTensorInvariantForm A hcof hA (b.rescale a ha) =
      coefficientTensorInvariantForm A hcof hA b := by
  unfold coefficientTensorInvariantForm
  rw [HarishChandraSchwartz.dualInvariantForm_rescale]
  exact b.tensorProduct_rescale_inv _ a ha

end Plancherel

end Langlands
