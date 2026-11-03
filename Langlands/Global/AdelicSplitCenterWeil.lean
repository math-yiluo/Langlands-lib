import Langlands.Global.AdelicSplitCenterSubgroupHaar
import Langlands.Analysis.Local.QuotientProductFactor

/-! # Full Weil compatibility on the actual positive/principal adelic quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Set Topology
open scoped CategoryTheory.MonObj Topology CompactlySupported

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints Langlands.QuotientIntegration

variable (F : Type u) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
variable (T : CommGroupScheme (Spec (CommRingCat.of F)))
variable (i : T.toGrp ⟶ G)
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (I : Type u) [Fintype I]
variable (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance (hc : IsCentral i) :
    IsMulRightInvariant (positiveRationalSubgroupHaarMeasure F G T i hi I e hc) :=
  positiveRationalSubgroupHaarMeasure_isMulRightInvariant F G T i hi I e hc

/-- Orbital integration over the full actual positive-times-principal subgroup. -/
def positiveRationalQuotientAverage (hc : IsCentral i) (f : AdelicGroupPoints F G → ℂ) :
    PositiveRationalQuotient F G T i → ℂ :=
  quotientAverage (positiveRationalSubgroup F G T i)
    (positiveRationalSubgroupHaarMeasure F G T i hi I e hc) f

@[simp] theorem positiveRationalQuotientAverage_mk (hc : IsCentral i)
    (f : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) :
    positiveRationalQuotientAverage F G T i hi I e hc f
      (LeftCosetSpace.mk (positiveRationalSubgroup F G T i) g) =
        ∫ h : positiveRationalSubgroup F G T i, f (h.val * g)
          ∂positiveRationalSubgroupHaarMeasure F G T i hi I e hc := rfl

/-- Every full subgroup fiber of an actual compact test is integrable. -/
theorem integrable_positiveRationalSubgroup_fiber (hc : IsCentral i)
    (f : AdelicGroupPoints F G → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (g : AdelicGroupPoints F G) :
    Integrable (fun h : positiveRationalSubgroup F G T i => f (h.val * g))
      (positiveRationalSubgroupHaarMeasure F G T i hi I e hc) := by
  let := positiveRationalSubgroupHaarMeasure_isHaarMeasure F G T i hi I e hc
  exact integrable_subgroup_mul_of_hasCompactSupport
    (positiveRationalSubgroup F G T i)
    (isClosed_positiveRationalSubgroup F G T i hi I e hc)
    (positiveRationalSubgroupHaarMeasure F G T i hi I e hc) f hf hfc g

variable [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

/-- The existing quotient measure satisfies the full subgroup Weil property,
with its fixed ambient and norm-one Haar normalizations. -/
theorem positiveRationalQuotientHaarMeasure_isCompatible (hc : IsCentral i) :
    IsCompatible (positiveRationalSubgroup F G T i)
      (Measure.haar : Measure (AdelicGroupPoints F G))
      (positiveRationalSubgroupHaarMeasure F G T i hi I e hc)
      (positiveRationalQuotientHaarMeasure F G T i) := by
  let := positiveIsTopologicalGroup F T I e
  let := positiveLocallyCompactSpace F T I e
  let := positiveSecondCountableTopology F T I e
  let : T2Space (intrinsicSubgroup F T) :=
    (positiveLogCoordinateEquiv F T I e).toHomeomorph.symm.t2Space
  let : PolishSpace (intrinsicSubgroup F T) := locallyCompactGroup_polishSpace _
  let := normalizedPositiveHaarMeasure_isHaarMeasure F G T i hi I e hc
  let := normalizedPositiveHaarMeasure_sigmaFinite F G T i hi I e hc
  let := normalizedPositiveHaarMeasure_isMulRightInvariant F G T i hi I e hc
  let := rationalNormOneSubgroup_count_isHaarMeasure F G
  let A := intrinsicSubgroup F T
  let H := rationalNormOneSubgroup F G
  let K := fullFactorSubgroup A H
  let E := normOneDecompositionMulEquiv F G T i hi I e hc
  let eH : K ≃ₜ* positiveRationalSubgroup F G T i :=
    (fullFactorSubgroupEquiv A H).symm.trans (positiveRationalDecomposition F G T i hi I e hc)
  let eQ : LeftQuotient K ≃ₜ PositiveRationalQuotient F G T i :=
    (fullFactorQuotientEquiv A H).trans (positiveQuotientHomeomorph F G T i hi I e hc)
  let : T2Space (LeftQuotient K) :=
    (fullFactorQuotientEquiv A H).symm.t2Space
  let : SecondCountableTopology (LeftQuotient K) :=
    (leftQuotient_isOpenQuotientMap K).secondCountableTopology
  let : BorelSpace (LeftQuotient K) := LeftCosetSpace.quotient_borelSpace K
  let := positiveRationalQuotient_borelSpace F G T i hi I e hc
  have heH : ∀ h : K, (eH h : AdelicGroupPoints F G) = E h.val := by
    intro h
    rfl
  have heQ : ∀ p : A × normOneSubgroup F G,
      eQ (Quotient.mk _ p) = Quotient.mk _ (E p) := by
    intro p
    change LeftCosetSpace.mk (positiveRationalSubgroup F G T i) p.2.val =
      LeftCosetSpace.mk (positiveRationalSubgroup F G T i)
        (positivePointMap F G T i p.1 * p.2.val)
    exact (LeftCosetSpace.mk_subgroup_mul (positiveRationalSubgroup F G T i)
      ⟨_, imageSubgroup_le_positiveRationalSubgroup F G T i
        ⟨p.1.val, p.1.property, rfl⟩⟩ p.2.val).symm
  have hprod := fullFactorQuotientMeasure_isCompatible A H
    (normalizedPositiveHaarMeasure F G T i hi I e hc) Measure.count
    (rationalNormOneSubgroup_isClosed F G)
    (Measure.haar : Measure (normOneSubgroup F G))
    (normOneRationalQuotientHaarMeasure F G)
    (normOneRationalQuotientHaarMeasure_isCompatible F G)
  have hmap := isCompatible_map_equiv E K (positiveRationalSubgroup F G T i)
    eH heH eQ heQ
    ((normalizedPositiveHaarMeasure F G T i hi I e hc).prod
      (Measure.haar : Measure (normOneSubgroup F G)))
    (fullFactorSubgroupMeasure A H
      (normalizedPositiveHaarMeasure F G T i hi I e hc) Measure.count)
    (fullFactorQuotientMeasure A H (normOneRationalQuotientHaarMeasure F G)) hprod
  have hamb : Measure.map E
      ((normalizedPositiveHaarMeasure F G T i hi I e hc).prod
        (Measure.haar : Measure (normOneSubgroup F G))) =
        (Measure.haar : Measure (AdelicGroupPoints F G)) :=
    map_normalizedPositiveHaarMeasure_prod F G T i hi I e hc
  have hsub : Measure.map eH
      (fullFactorSubgroupMeasure A H
        (normalizedPositiveHaarMeasure F G T i hi I e hc) Measure.count) =
        positiveRationalSubgroupHaarMeasure F G T i hi I e hc := by
    rw [fullFactorSubgroupMeasure,
      Measure.map_map
        (show Measurable (eH : K → positiveRationalSubgroup F G T i) from
          eH.continuous.measurable)
        (show Measurable (fullFactorSubgroupEquiv A H : A × H → K) from
          (fullFactorSubgroupEquiv A H).continuous.measurable)]
    rfl
  have hquot : Measure.map eQ
      (fullFactorQuotientMeasure A H (normOneRationalQuotientHaarMeasure F G)) =
        positiveRationalQuotientHaarMeasure F G T i := by
    rw [fullFactorQuotientMeasure,
      Measure.map_map eQ.continuous.measurable
        (fullFactorQuotientEquiv A H).symm.continuous.measurable]
    congr 1
    funext q
    exact congrArg (positiveQuotientHomeomorph F G T i hi I e hc)
      ((fullFactorQuotientEquiv A H).apply_symm_apply q)
  simpa only [hamb, hsub, hquot] using hmap

/-- The full subgroup average is integrable on the existing actual quotient. -/
theorem integrable_positiveRationalQuotientAverage (hc : IsCentral i)
    (f : AdelicGroupPoints F G → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (positiveRationalQuotientAverage F G T i hi I e hc f)
      (positiveRationalQuotientHaarMeasure F G T i) :=
  (positiveRationalQuotientHaarMeasure_isCompatible F G T i hi I e hc).averaging_integrable
    f hf hfc

/-- The exact full subgroup Weil formula with compact-test convergence. -/
theorem integral_positiveRationalQuotientAverage (hc : IsCentral i)
    (f : AdelicGroupPoints F G → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    (∫ q, positiveRationalQuotientAverage F G T i hi I e hc f q
      ∂positiveRationalQuotientHaarMeasure F G T i) =
        ∫ g, f g ∂(Measure.haar : Measure (AdelicGroupPoints F G)) :=
  (positiveRationalQuotientHaarMeasure_isCompatible F G T i hi I e hc).integral_formula
    f hf hfc

/-- Bundle the existing exact measure with its full subgroup compatibility. -/
def compatiblePositiveRationalQuotientHaarMeasure (hc : IsCentral i) :
    Subtype (fun ν : Measure (PositiveRationalQuotient F G T i) =>
      IsCompatible (positiveRationalSubgroup F G T i)
        (Measure.haar : Measure (AdelicGroupPoints F G))
        (positiveRationalSubgroupHaarMeasure F G T i hi I e hc) ν) :=
  ⟨positiveRationalQuotientHaarMeasure F G T i,
    positiveRationalQuotientHaarMeasure_isCompatible F G T i hi I e hc⟩

@[simp] theorem compatiblePositiveRationalQuotientHaarMeasure_val (hc : IsCentral i) :
    (compatiblePositiveRationalQuotientHaarMeasure F G T i hi I e hc).val =
      positiveRationalQuotientHaarMeasure F G T i := rfl

end Langlands.Global.PositiveRealTorus
