import Langlands.Automorphic.GroupSchemeRestrictionCuspidalL2
import Langlands.Automorphic.GroupSchemeRestrictionFullAEL2

/-! # Continuous parabolic-vanishing functions in the almost-everywhere cuspidal `L²` subspace
of the restriction split-centre quotient -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme PositiveRealTorus Langlands.Automorphic.GroupSchemeFunctions

variable (F : Type) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
variable (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
variable (S : CommGroupScheme (Spec (CommRingCat.of ℚ)))
variable (j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G)

local notation "measuresU" => properParabolicQuotientMeasure F G hPD hG

section Intrinsic

/-- For a continuous function, the integrand is the published constant-term integrand of its
pullback to adelic points. -/
theorem quotientParabolicPeriodIntegrand_eq_constantTermIntegrand
    (P : ProperRationalParabolic G) (f : C(Quotient F G S j, ℂ))
    (g : AdelicGroupPoints.normOneSubgroup F G) :
    quotientParabolicPeriodIntegrand F G hPD hG S j P f g =
      constantTermIntegrand F G (properRationalParabolicRadicals hPD hG P)
        (quotientContinuousPullback F G S j f) (g : AdelicGroupPoints F G) := by
  funext q
  induction q using Quotient.inductionOn with
  | _ n => exact quotientParabolicPeriodIntegrand_mk F G hPD hG S j P f g n

/-- The integral of a continuous function converges for every norm-one point. -/
theorem hasConvergentQuotientParabolicPeriod_of_continuous
    (P : ProperRationalParabolic G) (f : C(Quotient F G S j, ℂ))
    (g : AdelicGroupPoints.normOneSubgroup F G) :
    HasConvergentQuotientParabolicPeriod F G hPD hG S j P f g := by
  unfold HasConvergentQuotientParabolicPeriod
  rw [quotientParabolicPeriodIntegrand_eq_constantTermIntegrand]
  exact hasConvergentNormalizedParabolicConstantTerm F G hPD hG P
    (quotientContinuousPullback F G S j f) g

theorem quotientParabolicPeriod_eq_constantTerm
    (P : ProperRationalParabolic G) (f : C(Quotient F G S j, ℂ))
    (g : AdelicGroupPoints.normOneSubgroup F G) :
    quotientParabolicPeriod F G hPD hG S j P f g =
      constantTerm F G (properRationalParabolicRadicals hPD hG P) (measuresU P)
        (quotientContinuousPullback F G S j f) (g : AdelicGroupPoints F G) := by
  unfold quotientParabolicPeriod constantTerm
  rw [quotientParabolicPeriodIntegrand_eq_constantTermIntegrand]

/-- A continuous function whose constant terms for the mass-one measures vanish satisfies the
almost-everywhere condition (in fact at every norm-one point). -/
theorem isAEQuotientParabolicCuspidal_of_continuous (f : C(Quotient F G S j, ℂ))
    (hf : f ∈ quotientParabolicCuspidalSubrepresentation F G S j hPD hG measuresU) :
    IsAEQuotientParabolicCuspidal F G hPD hG S j f := by
  have hv := (mem_parabolicCuspidalSubrepresentation F G hPD hG measuresU
    (quotientContinuousPullback F G S j f)).mp hf
  intro P
  constructor
  · filter_upwards with g
    exact hasConvergentQuotientParabolicPeriod_of_continuous F G hPD hG S j P f g
  · filter_upwards with g
    change quotientParabolicPeriod F G hPD hG S j P f g = 0
    rw [quotientParabolicPeriod_eq_constantTerm]
    exact (hv P).2 g

end Intrinsic

section Canonical

variable {S j} {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (h : subgroup F G S j = imageSubgroup F T G i)
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (hc : IsCentral i) (hT : IsSplitTorus T.toGrp)

include h hi hc hT in
/-- For the canonical quotient measure, the condition depends only on the almost-everywhere
class of a strongly measurable function. -/
theorem isAEQuotientParabolicCuspidal_congr (φ ψ : Quotient F G S j → ℂ)
    (hφ : StronglyMeasurable φ) (hψ : StronglyMeasurable ψ)
    (heq : φ =ᵐ[quotientHaarMeasure F G S j] ψ) :
    IsAEQuotientParabolicCuspidal F G hPD hG S j φ ↔
      IsAEQuotientParabolicCuspidal F G hPD hG S j ψ := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  rw [isAEQuotientParabolicCuspidal_iff F G hPD hG h,
    isAEQuotientParabolicCuspidal_iff F G hPD hG h]
  exact mem_aeParabolicCuspidalFunctionSubmodule_congr F G hPD hG T i hi I e hc _ _
    (hφ.comp_measurable (quotientMeasurableEquiv F G h).measurable)
    (hψ.comp_measurable (quotientMeasurableEquiv F G h).measurable)
    ((measurePreserving_quotientMeasurableEquiv F G h).quasiMeasurePreserving.ae_eq_comp heq)

variable (hInv' : QuotientRightInvariant F G (quotientHaarMeasure F G S j))

/-- The `L²` class of a continuous square-integrable function with vanishing constant terms lies
in the almost-everywhere cuspidal subspace. -/
theorem quotientParabolicCuspidalL2ToLp_mem_fullAE
    (f : QuotientParabolicCuspidalL2Functions F G hPD hG measuresU
      (quotientHaarMeasure F G S j) hInv') :
    quotientParabolicCuspidalL2ToLp F G hPD hG measuresU _ hInv' f ∈
      quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT := by
  let := quotient_borelSpace F G hi h hc hT
  change IsAEQuotientParabolicCuspidal F G hPD hG S j _
  apply (isAEQuotientParabolicCuspidal_congr F G hPD hG h hi hc hT _ _
    (Lp.stronglyMeasurable _) f.val.continuous.stronglyMeasurable
    (coeFn_quotientParabolicCuspidalL2ToLp F G hPD hG measuresU _ hInv' f)).mpr
  exact isAEQuotientParabolicCuspidal_of_continuous F G hPD hG S j f.val f.property.1

section CuspForms

variable (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hrho : IsClosedSubgroup rho) (hK : Langlands.CompactIwasawa.IsMaximalCompact Kinf)
  (hN : 0 < N)

/-- The `L²` class of a square-integrable continuous `AdelicCuspidalForms` function lies in the
almost-everywhere cuspidal subspace. -/
theorem quotientCuspidalFormL2Image_le_fullAE (φ : Lp ℂ 2 (quotientHaarMeasure F G S j))
    (hφ : φ ∈ quotientCuspidalFormL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN _ hInv') :
    φ ∈ quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT := by
  obtain ⟨f, rfl⟩ := hφ
  exact quotientParabolicCuspidalL2ToLp_mem_fullAE F G hPD hG h hi hc hT hInv'
    (quotientCuspidalFormL2ToContinuousParabolic F G Kinf rho hsmooth hcalc hPD hG hrho hK hN _
      hInv' f)

end CuspForms

variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]

/-- Codomain restriction of the continuous parabolic-vanishing `L²` map. -/
def quotientParabolicCuspidalL2ToFullAE :
    (quotientParabolicCuspidalL2RightAction F G hPD hG measuresU _ hInv').IntertwiningMap
      (quotientFullAEL2CuspidalRightAction F G hPD hG h hi hc hT hInv') where
  toLinearMap :=
    (quotientParabolicCuspidalL2ToLp F G hPD hG measuresU _ hInv').toLinearMap.codRestrict
      (quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT)
      (quotientParabolicCuspidalL2ToLp_mem_fullAE F G hPD hG h hi hc hT hInv')
  isIntertwining' a := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _
      (quotientParabolicCuspidalL2ToLp F G hPD hG measuresU _ hInv') a f

/-- Forgetting the subspace recovers the continuous parabolic-vanishing `L²` map. -/
theorem quotientFullAEL2CuspidalToLp_comp_quotientParabolicCuspidalL2ToFullAE :
    (quotientFullAEL2CuspidalToLp F G hPD hG h hi hc hT hInv').comp
      (quotientParabolicCuspidalL2ToFullAE F G hPD hG h hi hc hT hInv') =
      quotientParabolicCuspidalL2ToLp F G hPD hG measuresU _ hInv' :=
  rfl

/-- Distinct continuous functions give distinct elements of the subspace. -/
theorem quotientParabolicCuspidalL2ToFullAE_injective :
    Function.Injective (quotientParabolicCuspidalL2ToFullAE F G hPD hG h hi hc hT hInv') := by
  let := quotientHaarMeasure_isOpenPosMeasure F G hi h hc hT
  intro f f' hf
  exact quotientParabolicCuspidalL2ToLp_injective F G hPD hG measuresU _ hInv'
    (congrArg Subtype.val hf)

/-- The image of continuous square-integrable parabolic-vanishing functions is contained in the
almost-everywhere cuspidal subrepresentation. -/
theorem quotientContinuousParabolicCuspidalL2Image_le_fullAE :
    quotientContinuousParabolicCuspidalL2Image F G hPD hG measuresU _ hInv' ≤
      quotientFullAEL2CuspidalSubrepresentation F G hPD hG h hi hc hT hInv' := by
  intro φ hφ
  obtain ⟨f, rfl⟩ := hφ
  exact quotientParabolicCuspidalL2ToLp_mem_fullAE F G hPD hG h hi hc hT hInv' f


end Canonical

section SplitComponents

variable {S j} {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (hj : IsSplitComponent j) (hs : IsSplitComponent i)
variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]

/-- For split components, the continuous parabolic-vanishing image is contained in the
almost-everywhere cuspidal subrepresentation. -/
theorem splitComponentParabolicCuspidalL2Image_le_fullAE :
    splitComponentParabolicCuspidalL2Image F G hi hj hs hPD hG measuresU ≤
      splitComponentFullAEL2CuspidalSubrepresentation F G hPD hG hi hj hs :=
  quotientContinuousParabolicCuspidalL2Image_le_fullAE F G hPD hG
    (subgroup_eq_of_splitComponents F G hj hs) hi hs.1.2 hs.1.1.1
    (quotientHaarMeasure_rightInvariant_of_splitComponents F G hi hj hs)

end SplitComponents

end Langlands.Global.RestrictionSplitCentre
