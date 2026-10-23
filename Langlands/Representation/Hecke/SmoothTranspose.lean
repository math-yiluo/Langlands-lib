import Langlands.Representation.Hecke.IntegratedAction
import Langlands.Representation.Smooth.Contragredient.LawsProof
import Mathlib.MeasureTheory.Group.Integral

/-!
Restrict the algebraic transpose of an actual Hecke operator to the actual
smooth dual. Inversion invariance of the measure is an explicit hypothesis.
-/

noncomputable section

namespace Langlands.Hecke

open HarmonicAnalysis MeasureTheory MeasureTheory.Measure

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsInvInvariant μ]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

/-- The actual integrated smooth-contragredient action is adjoint to the
original action with its test function inverted. -/
theorem integratedAction_smoothDualPairing (f : SchwartzBruhat G)
    (ℓ : SmoothDual ρ) (v : V) :
    smoothDualPairing ρ
        (integratedAction μ (smoothContragredient ρ)
          (isSmooth_smoothContragredient ρ) f ℓ) v =
      smoothDualPairing ρ ℓ (integratedAction μ ρ hρ (TestFunction.inversion f) v) := by
  let ev : SmoothDual ρ →ₗ[ℂ] ℂ :=
    (Module.Dual.eval ℂ V v).comp (smoothDualPairing ρ)
  change ev (integratedAction μ (smoothContragredient ρ)
    (isSmooth_smoothContragredient ρ) f ℓ) = _
  rw [integratedAction_dual, integratedAction_dual]
  change (∫ g, f g * smoothDualPairing ρ ℓ (ρ g⁻¹ v) ∂μ) =
    ∫ g, f g⁻¹ * smoothDualPairing ρ ℓ (ρ g v) ∂μ
  simpa only [inv_inv] using
    (integral_inv_eq_self
      (fun g => f g⁻¹ * smoothDualPairing ρ ℓ (ρ g v)) μ)

/-- Transposing an actual Hecke operator preserves smooth functionals. -/
theorem integratedAction_dualMap_mem_smoothVectors (f : SchwartzBruhat G)
    (ℓ : SmoothDual ρ) :
    (integratedAction μ ρ hρ f).dualMap (smoothDualPairing ρ ℓ) ∈
      smoothVectors ρ.dual := by
  have heq :
      (integratedAction μ ρ hρ f).dualMap (smoothDualPairing ρ ℓ) =
        smoothDualPairing ρ
          (integratedAction μ (smoothContragredient ρ)
            (isSmooth_smoothContragredient ρ) (TestFunction.inversion f) ℓ) := by
    ext v
    simpa only [TestFunction.inversion_inversion, LinearMap.dualMap_apply] using
      (integratedAction_smoothDualPairing μ ρ hρ (TestFunction.inversion f) ℓ v).symm
  rw [heq]
  exact (integratedAction μ (smoothContragredient ρ)
    (isSmooth_smoothContragredient ρ) (TestFunction.inversion f) ℓ).property

/-- The algebraic transpose of the original operator, restricted to smooth
functionals and bundled linearly in the original test function. -/
def integratedTranspose : SchwartzBruhat G →ₗ[ℂ] Module.End ℂ (SmoothDual ρ) where
  toFun f :=
    ((integratedAction μ ρ hρ f).dualMap.comp (smoothDualPairing ρ)).codRestrict
      (smoothVectors ρ.dual) (integratedAction_dualMap_mem_smoothVectors μ ρ hρ f)
  map_add' f g := by
    ext ℓ v
    change smoothDualPairing ρ ℓ (integratedAction μ ρ hρ (f + g) v) = _
    simp only [map_add, LinearMap.add_apply]
    rfl
  map_smul' c f := by
    ext ℓ v
    change smoothDualPairing ρ ℓ (integratedAction μ ρ hρ (c • f) v) = _
    simp only [map_smul, LinearMap.smul_apply]
    rfl

@[simp]
theorem integratedTranspose_pairing (f : SchwartzBruhat G)
    (ℓ : SmoothDual ρ) (v : V) :
    smoothDualPairing ρ (integratedTranspose μ ρ hρ f ℓ) v =
      smoothDualPairing ρ ℓ (integratedAction μ ρ hρ f v) := rfl

/-- Forgetting smoothness gives exactly the algebraic transpose, with no
replacement of the underlying functional. -/
theorem smoothDualPairing_comp_integratedTranspose (f : SchwartzBruhat G) :
    (smoothDualPairing ρ).comp (integratedTranspose μ ρ hρ f) =
      (integratedAction μ ρ hρ f).dualMap.comp (smoothDualPairing ρ) := rfl

/-- The restricted transpose is the actual smooth-contragredient operator
for the inverted test function. -/
theorem integratedTranspose_eq_integratedAction_inversion (f : SchwartzBruhat G) :
    integratedTranspose μ ρ hρ f =
      integratedAction μ (smoothContragredient ρ)
        (isSmooth_smoothContragredient ρ) (TestFunction.inversion f) := by
  ext ℓ v
  change smoothDualPairing ρ ℓ (integratedAction μ ρ hρ f v) =
    smoothDualPairing ρ
      (integratedAction μ (smoothContragredient ρ)
        (isSmooth_smoothContragredient ρ) (TestFunction.inversion f) ℓ) v
  simpa only [TestFunction.inversion_inversion] using
    (integratedAction_smoothDualPairing μ ρ hρ (TestFunction.inversion f) ℓ v).symm

end Langlands.Hecke
