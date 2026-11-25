import Langlands.Analysis.Local.CompactQuotientSmoothTraceClassReduction
import Langlands.Automorphic.GroupSchemeFullAEL2CuspidalSmoothTraceClassStatement
import Langlands.Global.AdelicDixmierMalliavin
import Langlands.Representation.Unitary.IntegratedConvolutionStatement

/-!
# Cuspidal trace class of smooth test functions, from the convolution identity

`groupSchemeFullAEL2CuspidalSmoothTraceClass_of_convolution` proves
`GroupSchemeFullAEL2CuspidalSmoothTraceClassStatement` from
`IntegratedActionConvolutionStatement` (`R(φ ⋆ ψ) = R(φ) ∘ R(ψ)`), the Dixmier–Malliavin
factorization of adelic test functions, and the trace class of products of two Hilbert–Schmidt
operators.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme Langlands.Analysis

/-- `GroupSchemeFullAEL2CuspidalSmoothTraceClassStatement` follows from the convolution identity
`IntegratedActionConvolutionStatement`: a test function is a finite sum of convolutions `φᵢ ⋆ ψᵢ` of
test functions (`IsAdelicTestFunction.exists_eq_sum_convolution`), each `R_cusp(φᵢ ⋆ ψᵢ)` is
`R_cusp(φᵢ) ∘ R_cusp(ψᵢ)`, a product of two Hilbert–Schmidt operators, hence trace class, and
trace-class operators add up. -/
theorem groupSchemeFullAEL2CuspidalSmoothTraceClass_of_convolution
    (hconv : IntegratedActionConvolutionStatement.{u, u}) :
    GroupSchemeFullAEL2CuspidalSmoothTraceClassStatement.{u} := by
  intro F _ _ G _ _ hPD hG T i hi _ I _ e hc _ μG hHS f hf htest
  obtain ⟨n, φ, ψ, hφψ, hsum⟩ := htest.exists_eq_sum_convolution hG
  have hint : ∀ w : C_c(AdelicGroupPoints F G, ℂ), Integrable w μG := fun w =>
    w.continuous.integrable_of_hasCompactSupport w.hasCompactSupport
  set πc := fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
  have hπcnorm := norm_fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
  have hπcmeas := fullAEL2CuspidalOrbit_aestronglyMeasurable F G hPD hG T i hi I e hc μG
  have hpiece : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      ∃ h : Integrable (fun g => ∫ a, φ j a * ψ j (a⁻¹ * g) ∂μG) μG,
        OperatorIdeals.IsTraceClass (integratedIsometricAction μG πc hπcnorm hπcmeas
          (fun g => ∫ a, φ j a * ψ j (a⁻¹ * g) ∂μG) h) := by
    intro j _
    obtain ⟨h, heq⟩ := hconv (AdelicGroupPoints F G) _ μG πc hπcnorm hπcmeas (φ j) (ψ j)
      (hint _) (hint _)
    refine ⟨h, ?_⟩
    rw [heq]
    exact OperatorIdeals.hilbertSchmidtProductTraceClass _ _ _ _
      (hHS (ψ j) (hint _) (hφψ j).2) (hHS (φ j) (hint _) (hφψ j).1)
  obtain ⟨hI, htc⟩ := exists_isTraceClass_integratedIsometricAction_finsetSum μG πc hπcnorm
    hπcmeas Finset.univ _ hpiece
  have hf' : (f : AdelicGroupPoints F G → ℂ) =
      ∑ j, fun g => ∫ a, φ j a * ψ j (a⁻¹ * g) ∂μG := by
    funext g
    rw [hsum g, Finset.sum_apply]
  change OperatorIdeals.IsTraceClass (integratedIsometricAction μG πc hπcnorm hπcmeas f hf)
  rwa [integratedIsometricAction_congr μG πc hπcnorm hπcmeas hf' hf hI]

end Langlands.Automorphic.GroupSchemeFunctions
