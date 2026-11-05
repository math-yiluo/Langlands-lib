import Langlands.Global.AdelicSplitComponentHaar
import Langlands.Global.AdelicSplitCenterWeil

/-! # Intrinsic orbital averaging and change of actual split component -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints Langlands.QuotientIntegration

variable (F : Type u) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
variable (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The intrinsic full subgroup normalization is right invariant. -/
theorem intrinsicPositiveRationalSubgroupHaarMeasure_isMulRightInvariant
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp) :
    IsMulRightInvariant (intrinsicPositiveRationalSubgroupHaarMeasure F G T i hi hc hT) := by
  let : Finite hT.choose := hT.choose_spec.1
  let := Fintype.ofFinite hT.choose
  unfold intrinsicPositiveRationalSubgroupHaarMeasure
  exact positiveRationalSubgroupHaarMeasure_isMulRightInvariant F G T i hi _ _ hc

local instance (hc : IsCentral i) (hT : IsSplitTorus T.toGrp) :
    IsMulRightInvariant (intrinsicPositiveRationalSubgroupHaarMeasure F G T i hi hc hT) :=
  intrinsicPositiveRationalSubgroupHaarMeasure_isMulRightInvariant F G T i hi hc hT

/-- Actual full subgroup orbital averaging, with no supplied splitting coordinates. -/
def intrinsicPositiveRationalQuotientAverage (hc : IsCentral i) (hT : IsSplitTorus T.toGrp)
    (f : AdelicGroupPoints F G → ℂ) : PositiveRationalQuotient F G T i → ℂ :=
  quotientAverage (positiveRationalSubgroup F G T i)
    (intrinsicPositiveRationalSubgroupHaarMeasure F G T i hi hc hT) f

@[simp] theorem intrinsicPositiveRationalQuotientAverage_mk
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp)
    (f : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) :
    intrinsicPositiveRationalQuotientAverage F G T i hi hc hT f
      (LeftCosetSpace.mk (positiveRationalSubgroup F G T i) g) =
        ∫ h : positiveRationalSubgroup F G T i, f (h.val * g)
          ∂intrinsicPositiveRationalSubgroupHaarMeasure F G T i hi hc hT := rfl

/-- Every finite splitting gives exactly the same intrinsic orbital average. -/
theorem intrinsicPositiveRationalQuotientAverage_eq
    (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp) (f : AdelicGroupPoints F G → ℂ) :
    intrinsicPositiveRationalQuotientAverage F G T i hi hc hT f =
      positiveRationalQuotientAverage F G T i hi I e hc f := by
  funext q
  induction q using Quotient.inductionOn with
  | _ g =>
    change (∫ h : positiveRationalSubgroup F G T i, f (h.val * g)
      ∂intrinsicPositiveRationalSubgroupHaarMeasure F G T i hi hc hT) =
        ∫ h : positiveRationalSubgroup F G T i, f (h.val * g)
          ∂positiveRationalSubgroupHaarMeasure F G T i hi I e hc
    rw [intrinsicPositiveRationalSubgroupHaarMeasure_eq F G T i hi I e hc hT]

/-- Compact test functions have integrable intrinsic full subgroup fibers. -/
theorem integrable_intrinsicPositiveRationalSubgroup_fiber
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp)
    (f : AdelicGroupPoints F G → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (g : AdelicGroupPoints F G) :
    Integrable (fun h : positiveRationalSubgroup F G T i => f (h.val * g))
      (intrinsicPositiveRationalSubgroupHaarMeasure F G T i hi hc hT) := by
  let : Finite hT.choose := hT.choose_spec.1
  let := Fintype.ofFinite hT.choose
  rw [intrinsicPositiveRationalSubgroupHaarMeasure_eq F G T i hi hT.choose
    (Classical.choice hT.choose_spec.2) hc hT]
  exact integrable_positiveRationalSubgroup_fiber F G T i hi _ _ hc f hf hfc g

section Weil

variable [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

/-- The existing exact quotient measure is compatible with intrinsic full subgroup Haar. -/
theorem intrinsicPositiveRationalQuotientHaarMeasure_isCompatible
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp) :
    IsCompatible (positiveRationalSubgroup F G T i)
      (Measure.haar : Measure (AdelicGroupPoints F G))
      (intrinsicPositiveRationalSubgroupHaarMeasure F G T i hi hc hT)
      (positiveRationalQuotientHaarMeasure F G T i) := by
  let : Finite hT.choose := hT.choose_spec.1
  let := Fintype.ofFinite hT.choose
  simpa only [intrinsicPositiveRationalSubgroupHaarMeasure_eq F G T i hi hT.choose
    (Classical.choice hT.choose_spec.2) hc hT] using
    positiveRationalQuotientHaarMeasure_isCompatible F G T i hi hT.choose
      (Classical.choice hT.choose_spec.2) hc

/-- The intrinsic average of every compact test is integrable on the actual quotient. -/
theorem integrable_intrinsicPositiveRationalQuotientAverage
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp)
    (f : AdelicGroupPoints F G → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (intrinsicPositiveRationalQuotientAverage F G T i hi hc hT f)
      (positiveRationalQuotientHaarMeasure F G T i) :=
  (intrinsicPositiveRationalQuotientHaarMeasure_isCompatible F G T i hi hc hT).averaging_integrable
    f hf hfc

/-- The intrinsic full subgroup Weil formula, with compact-test convergence. -/
theorem integral_intrinsicPositiveRationalQuotientAverage
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp)
    (f : AdelicGroupPoints F G → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    (∫ q, intrinsicPositiveRationalQuotientAverage F G T i hi hc hT f q
      ∂positiveRationalQuotientHaarMeasure F G T i) =
        ∫ g, f g ∂(Measure.haar : Measure (AdelicGroupPoints F G)) :=
  (intrinsicPositiveRationalQuotientHaarMeasure_isCompatible F G T i hi hc hT).integral_formula
    f hf hfc

end Weil

variable (T' : CommGroupScheme (Spec (CommRingCat.of F))) (i' : T'.toGrp ⟶ G)
variable (hi' : Function.Injective (characterRestrict i'))
variable [(characterRestrict i').range.FiniteIndex]

/-- Integrability of arbitrary actual subgroup fibers is unchanged by split-component change. -/
theorem integrable_intrinsicPositiveRationalSubgroup_fiber_iff
    (hs : IsSplitComponent i) (hs' : IsSplitComponent i')
    (f : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) :
    Integrable (fun h : positiveRationalSubgroup F G T i => f (h.val * g))
      (intrinsicPositiveRationalSubgroupHaarMeasure F G T i hi hs.1.2 hs.1.1.1) ↔
    Integrable (fun h : positiveRationalSubgroup F G T' i' => f (h.val * g))
      (intrinsicPositiveRationalSubgroupHaarMeasure F G T' i' hi' hs'.1.2 hs'.1.1.1) := by
  have hp := measurePreserving_splitComponentSubgroupEquiv_intrinsic
    F G T i hi T' i' hi' hs hs'
  exact hp.integrable_comp_emb
    (splitComponentSubgroupEquiv F G T i T' i' hs hs').toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (g := fun h : positiveRationalSubgroup F G T' i' => f (h.val * g))

/-- Intrinsic orbital averages agree under the identity on actual quotient representatives. -/
theorem intrinsicPositiveRationalQuotientAverage_splitComponent
    (hs : IsSplitComponent i) (hs' : IsSplitComponent i')
    (f : AdelicGroupPoints F G → ℂ) (q : PositiveRationalQuotient F G T i) :
    intrinsicPositiveRationalQuotientAverage F G T' i' hi' hs'.1.2 hs'.1.1.1 f
      (splitComponentQuotientMeasurableEquiv F G hs hs' q) =
        intrinsicPositiveRationalQuotientAverage F G T i hi hs.1.2 hs.1.1.1 f q := by
  induction q using Quotient.inductionOn with
  | _ g =>
    change intrinsicPositiveRationalQuotientAverage F G T' i' hi' hs'.1.2 hs'.1.1.1 f
      (splitComponentQuotientMeasurableEquiv F G hs hs'
        (LeftCosetSpace.mk (positiveRationalSubgroup F G T i) g)) =
          intrinsicPositiveRationalQuotientAverage F G T i hi hs.1.2 hs.1.1.1 f
            (LeftCosetSpace.mk (positiveRationalSubgroup F G T i) g)
    rw [splitComponentQuotientMeasurableEquiv_mk F G hs hs' g]
    change (∫ h : positiveRationalSubgroup F G T' i', f (h.val * g)
      ∂intrinsicPositiveRationalSubgroupHaarMeasure F G T' i' hi' hs'.1.2 hs'.1.1.1) =
        ∫ h : positiveRationalSubgroup F G T i, f (h.val * g)
          ∂intrinsicPositiveRationalSubgroupHaarMeasure F G T i hi hs.1.2 hs.1.1.1
    have hp := measurePreserving_splitComponentSubgroupEquiv_intrinsic
      F G T i hi T' i' hi' hs hs'
    exact (hp.integral_comp
      (splitComponentSubgroupEquiv F G T i T' i' hs hs').toHomeomorph.toMeasurableEquiv.measurableEmbedding
      (fun h : positiveRationalSubgroup F G T' i' => f (h.val * g))).symm

/-- Integrability of arbitrary intrinsic averages on the actual quotient is independent. -/
theorem integrable_intrinsicPositiveRationalQuotientAverage_iff
    (hs : IsSplitComponent i) (hs' : IsSplitComponent i')
    (f : AdelicGroupPoints F G → ℂ) :
    Integrable (intrinsicPositiveRationalQuotientAverage F G T i hi hs.1.2 hs.1.1.1 f)
      (positiveRationalQuotientHaarMeasure F G T i) ↔
    Integrable (intrinsicPositiveRationalQuotientAverage F G T' i' hi' hs'.1.2 hs'.1.1.1 f)
      (positiveRationalQuotientHaarMeasure F G T' i') := by
  have hp := measurePreserving_splitComponentQuotient F G hs hs'
  have h := hp.integrable_comp_emb
    (splitComponentQuotientMeasurableEquiv F G hs hs').measurableEmbedding
    (g := intrinsicPositiveRationalQuotientAverage F G T' i' hi' hs'.1.2 hs'.1.1.1 f)
  simpa only [Function.comp_def,
    intrinsicPositiveRationalQuotientAverage_splitComponent F G T i hi T' i' hi' hs hs'] using h

/-- Total integrals of the two intrinsic averages agree for the fixed quotient measures. -/
theorem integral_intrinsicPositiveRationalQuotientAverage_splitComponent
    (hs : IsSplitComponent i) (hs' : IsSplitComponent i')
    (f : AdelicGroupPoints F G → ℂ) :
    (∫ q, intrinsicPositiveRationalQuotientAverage F G T' i' hi' hs'.1.2 hs'.1.1.1 f q
      ∂positiveRationalQuotientHaarMeasure F G T' i') =
    ∫ q, intrinsicPositiveRationalQuotientAverage F G T i hi hs.1.2 hs.1.1.1 f q
      ∂positiveRationalQuotientHaarMeasure F G T i := by
  have hp := measurePreserving_splitComponentQuotient F G hs hs'
  calc
    _ = ∫ q, intrinsicPositiveRationalQuotientAverage F G T' i' hi' hs'.1.2 hs'.1.1.1 f
        (splitComponentQuotientMeasurableEquiv F G hs hs' q)
        ∂positiveRationalQuotientHaarMeasure F G T i :=
      (hp.integral_comp' _).symm
    _ = _ := by
      congr 1
      funext q
      exact intrinsicPositiveRationalQuotientAverage_splitComponent
        F G T i hi T' i' hi' hs hs' f q

end Langlands.Global.PositiveRealTorus
