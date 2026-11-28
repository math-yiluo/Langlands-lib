import Langlands.Automorphic.GroupSchemeQuotientL2SmoothRepresentativeStatement
import Langlands.Automorphic.GroupSchemePositiveQuotientL2Smoothing

/-! # Smooth representatives of adelic quotient convolution -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.InfiniteAdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme

/-- The pointwise smoothing of an `L²` class represents the original quotient
convolution, with each orbit derivative given by a differentiated test kernel. -/
theorem groupSchemeQuotientL2SmoothRepresentative :
    GroupSchemeQuotientL2SmoothRepresentativeStatement.{u} := by
  intro F _ _ G _ _ T i hi _ I _ e hc _ d hsmooth
  dsimp only
  intro f hf htest φ
  let H := positiveRationalSubgroup F G T i
  let μG : Measure (AdelicGroupPoints F G) := Measure.haar
  let Φ := fun x => φ (LeftCosetSpace.mk H x)
  let ψ := rightConvolution F G f Φ
  let := positiveRationalQuotient_borelSpace F G T i hi I e hc
  have hΦ : Measurable Φ :=
    (Lp.stronglyMeasurable φ).measurable.comp (LeftCosetSpace.continuous_mk H).measurable
  have hΦloc : LocallyIntegrable Φ μG :=
    locallyIntegrable_positiveQuotientLpPullback T i hi I e hc φ
  have hψ : IsAdelicSmoothFunction F G ψ :=
    (adelicRightConvolutionDifferentiation F G d hsmooth f Φ htest hΦ hΦloc).2.1
  refine ⟨hΦloc, hψ, ?_, ?_⟩
  · intro s
    induction s with
    | nil => exact ⟨htest, Set.Subset.rfl, rfl⟩
    | cons X s hs =>
      obtain ⟨hk, hkSupp, hEq⟩ := hs
      let k := s.foldr (rightConvolutionKernelDerivative hsmooth) f
      obtain ⟨hk', hk'Supp⟩ := rightConvolutionKernelDerivative_isTestFunction hsmooth X hk
      refine ⟨hk', hk'Supp.trans hkSupp, ?_⟩
      rw [adelicIteratedDirectionalValue_cons, hEq]
      funext x
      rw [← pair_projections F G x, adelicDirectionalValue_pair]
      exact (adelicRightConvolutionDifferentiation F G d hsmooth k Φ hk hΦ hΦloc).2.2 X _ _
  · have hleft : ∀ (h : H) (x : AdelicGroupPoints F G), ψ (h.val * x) = ψ x :=
      positiveQuotientLpSmoothing_invariant T i f φ
    let ψQ : C(PositiveRationalQuotient F G T i, ℂ) :=
      ⟨LeftCosetSpace.lift H ψ hleft, LeftCosetSpace.continuous_lift H ψ hleft hψ.1⟩
    exact ⟨ψQ, fun _ => rfl, positiveQuotientLpSmoothing_ae_eq T i hi I e hc f hf φ⟩

end Langlands.Automorphic.GroupSchemeFunctions
