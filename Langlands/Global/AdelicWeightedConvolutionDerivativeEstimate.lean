import Langlands.Global.AdelicRightConvolutionEnveloping
import Langlands.Global.AdelicWeightedPointwiseConvolution
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # A common growth exponent for the weighted convolution derivatives -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Global

open AdelicGroupPoints RepresentationGrowth WeightedSiegel
  Langlands.Automorphic.GroupSchemeFunctions InfiniteAdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
  {n d : ℕ} (rho : GroupScheme.MatrixRepresentation G (Fin n))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

local notation "UEA" => AdelicEnvelopingAlgebra F G hsmooth
local notation "μG" => (Measure.haar : Measure (AdelicGroupPoints F G))

/-- The whole enveloping algebra of the right convolution has one weighted growth exponent
on compact finite slices, uniform over all compact kernel supports. -/
def AdelicWeightedConvolutionDerivativeEstimateStatement : Prop :=
  0 < n → GroupScheme.IsClosedSubgroup rho →
  ∀ (ell : RealCharacterDual F P → ℝ), Continuous ell →
  ∀ (A r : ℝ), 0 < A → 0 ≤ r →
  (∀ g, Real.exp (ell (hK.height g)) ≤ A * adelicHeight F G rho g ^ r) →
  let Γ := parabolicPrincipalSubgroup F p
  let D := LeftCosetSpace.fundamentalDomain Γ (isDiscrete_parabolicPrincipalSubgroup F p)
  ∃ R : ℝ, 0 ≤ R ∧ ∀ (Kf : Set (FiniteAdelicGroupPoints F G)), IsCompact Kf →
    ∀ (h : AdelicGroupPoints F G → ℂ) (hh : IsAdelicTestFunction F G h) (a : UEA),
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (S : Set (RealCharacterDual F P)), @MeasurableSet _ (borel _) S →
      ∀ x : AdelicGroupPoints F G, finite F G x ∈ Kf →
      (∀ g ∈ tsupport h, hK.height (x * g) ∈ S) →
      ∀ (f : AdelicGroupPoints F G → ℂ) (hf : Measurable f) (hfi : LocallyIntegrable f μG),
      (∀ (dlt : Γ) g, f ((dlt : AdelicGroupPoints F G) * g) = f g) →
      let I := ∫⁻ g in D, ‖f g‖ₑ ^ (2 : ℕ) * chamberDensity F p hK ell S g ∂μG
      I < ∞ →
      ‖(plotSmoothEnvelopingAction F G hsmooth hcalc a
        (rightConvolutionSmoothSlice hsmooth h f hh hf hfi (finite F G x))).val
          (infinite F G x)‖ ≤ B * adelicHeight F G rho x ^ R * Real.sqrt I.toReal

theorem adelicWeightedConvolutionDerivativeEstimate :
    AdelicWeightedConvolutionDerivativeEstimateStatement hK rho hsmooth hcalc := by
  intro hn hrho ell hell A r hA hr hweight Γ D
  obtain ⟨R, hR, hbound⟩ := adelicWeightedPointwiseConvolution F G P p K hK n rho hn hrho
    ell hell A r hA hr hweight
  refine ⟨R, hR, fun Kf hKf h hh a => ?_⟩
  obtain ⟨k, hk, hks, heq⟩ := adelicRightConvolutionEnveloping hsmooth hcalc a h hh
  obtain ⟨B, hB, hb⟩ := hbound Kf hKf (tsupport h) hh.2.1
  have hkL2 : MemLp k 2 ((μG).restrict (tsupport h)) :=
    hk.1.1.memLp_of_hasCompactSupport hk.2.1
  refine ⟨B * ‖hkL2.toLp k‖, mul_nonneg hB (norm_nonneg _), ?_⟩
  intro S hS x hx hxC f hf hfi hfΓ I hI
  rw [heq f hf hfi (finite F G x)]
  change ‖rightConvolution F G k f (pair F G (infinite F G x) (finite F G x))‖ ≤ _
  rw [pair_projections]
  have hest : ‖rightConvolution F G k f x‖ ≤
      B * adelicHeight F G rho x ^ R * ‖hkL2.toLp k‖ * Real.sqrt I.toReal :=
    (hb S hS x hx hxC f hf hfΓ hI k hkL2 ((subset_tsupport k).trans hks)).2
  exact hest.trans_eq (by ring)

end Langlands.Global
