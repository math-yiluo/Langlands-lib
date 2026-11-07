import Langlands.Automorphic.GroupSchemeRestrictionQuotientL2FiniteAverage
import Langlands.Automorphic.GroupSchemeQuotientL2InfiniteAction

/-! # The infinite adelic action on `L²` of the restriction split-centre quotient `[G]` -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme PositiveRealTorus Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis

variable (F : Type) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
variable {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
variable {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G}
variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}

section Infinite

variable (measureQ : Measure (Quotient F G S j))
variable (hInv : QuotientRightInvariant F G measureQ)

local notation "π" => rationalQuotientL2BoundedRightAction F G measureQ hInv

/-- The bounded right action on `L²([G])`, restricted along the actual inclusion of the
infinite adelic points. -/
def rationalQuotientL2InfiniteRightAction :
    InfiniteAdelicGroupPoints F G →* (Lp ℂ 2 measureQ →L[ℂ] Lp ℂ 2 measureQ) :=
  (π).comp (AdelicGroupPoints.ofInfinite F G).toMonoidHom

local notation "π∞" => rationalQuotientL2InfiniteRightAction F G measureQ hInv

@[simp]
theorem rationalQuotientL2InfiniteRightAction_apply (a : InfiniteAdelicGroupPoints F G)
    (φ : Lp ℂ 2 measureQ) :
    π∞ a φ =
      rationalQuotientL2RightAction F G measureQ hInv (AdelicGroupPoints.ofInfinite F G a) φ :=
  rfl

theorem norm_rationalQuotientL2InfiniteRightAction (a : InfiniteAdelicGroupPoints F G)
    (φ : Lp ℂ 2 measureQ) : ‖π∞ a φ‖ = ‖φ‖ :=
  norm_rationalQuotientL2BoundedRightAction F G measureQ hInv _ φ

/-- The actions of the finite and of the infinite adelic points on `L²([G])` commute. -/
theorem rationalQuotientL2InfiniteFinite_commute (a : InfiniteAdelicGroupPoints F G)
    (b : FiniteAdelicGroupPoints F G) (φ : Lp ℂ 2 measureQ) :
    π∞ a (rationalQuotientL2FiniteRightAction F G measureQ hInv b φ) =
      rationalQuotientL2FiniteRightAction F G measureQ hInv b (π∞ a φ) := by
  change π (AdelicGroupPoints.ofInfinite F G a) (π (AdelicGroupPoints.ofFinite F G b) φ) =
    π (AdelicGroupPoints.ofFinite F G b) (π (AdelicGroupPoints.ofInfinite F G a) φ)
  exact congrArg (fun A : Lp ℂ 2 measureQ →L[ℂ] Lp ℂ 2 measureQ => A φ)
    ((AdelicGroupPoints.factors_commute F G a b).map π).eq

end Infinite

variable (h : subgroup F G S j = imageSubgroup F T G i)
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]
variable (hc : IsCentral i) (hT : IsSplitTorus T.toGrp)
variable (hInv' : QuotientRightInvariant F G (quotientHaarMeasure F G S j))

local notation "μ" => quotientHaarMeasure F G S j
local notation "π∞G" =>
  rationalQuotientL2InfiniteRightAction F G (quotientHaarMeasure F G S j) hInv'

include h hi hc hT in
/-- For the canonical measure, every orbit of the infinite adelic points is continuous. -/
theorem continuous_rationalQuotientL2InfiniteOrbit (φ : Lp ℂ 2 μ) :
    Continuous (fun a : InfiniteAdelicGroupPoints F G => π∞G a φ) :=
  (rationalQuotientL2OrbitMap F G hInv' h hi hc hT φ).continuous.comp
    (AdelicGroupPoints.ofInfinite F G).continuous

include h hi hc hT in
/-- For the canonical measure, infinite orbits are almost everywhere strongly measurable for
every measure on the infinite adelic points. -/
theorem rationalQuotientL2InfiniteOrbit_aestronglyMeasurable
    (ν : Measure (InfiniteAdelicGroupPoints F G)) (φ : Lp ℂ 2 μ) :
    AEStronglyMeasurable (fun a : InfiniteAdelicGroupPoints F G => π∞G a φ) ν :=
  (continuous_rationalQuotientL2InfiniteOrbit F G h hi hc hT hInv' φ).stronglyMeasurable
    |>.aestronglyMeasurable

/-- `quotientL2Equiv` carries the published positive-torus infinite action to the infinite
action on `[G]`. -/
theorem quotientL2Equiv_infiniteRightAction (I : Type) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (a : InfiniteAdelicGroupPoints F G)
    (φ : QuotientL2 F G T i (positiveRationalQuotientHaarMeasure F G T i)) :
    quotientL2Equiv F G h (haarQuotientL2InfiniteRightAction F G T i hi I e hc a φ) =
      π∞G a (quotientL2Equiv F G h φ) :=
  quotientL2Equiv_rightAction F G h (haarQuotientMeasureRightInvariant F G T i hi I e hc) hInv'
    _ φ

section Average

variable (K : OpenSubgroup (FiniteAdelicGroupPoints F G)) [CompactSpace K]

attribute [local instance] finiteAverageTopologicalGroup finiteAverageSecondCountable
  finiteAverageMeasurableSpace finiteAverageBorelSpace

/-- Averaging over a compact open subgroup of the finite adelic points intertwines the infinite
action on `[G]`. -/
theorem rationalQuotientL2FiniteAverage_infiniteRightAction (a : InfiniteAdelicGroupPoints F G)
    (φ : Lp ℂ 2 μ) :
    π∞G a (rationalQuotientL2FiniteAverage F G h hi hc hT hInv' K φ) =
      rationalQuotientL2FiniteAverage F G h hi hc hT hInv' K (π∞G a φ) :=
  compactIsometricAverage_intertwiner K
    (rationalQuotientL2CompactOpenAction F G μ hInv' K)
    (norm_rationalQuotientL2CompactOpenAction F G μ hInv' K)
    (continuous_rationalQuotientL2CompactOpenOrbit F G h hi hc hT hInv' K)
    (rationalQuotientL2CompactOpenAction F G μ hInv' K)
    (norm_rationalQuotientL2CompactOpenAction F G μ hInv' K)
    (continuous_rationalQuotientL2CompactOpenOrbit F G h hi hc hT hInv' K)
    (π∞G a) (fun k x => rationalQuotientL2InfiniteFinite_commute F G μ hInv' a k x) φ

end Average

section SplitComponents

variable (hj : IsSplitComponent j) (hs : IsSplitComponent i)

local notation "hInvS" => quotientHaarMeasure_rightInvariant_of_splitComponents F G hi hj hs
local notation "hS" => subgroup_eq_of_splitComponents F G hj hs

/-- For split components, the infinite adelic action on `L²([G])`. -/
def splitComponentL2InfiniteRightAction :
    InfiniteAdelicGroupPoints F G →* (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  rationalQuotientL2InfiniteRightAction F G μ hInvS

@[simp]
theorem splitComponentL2InfiniteRightAction_apply (a : InfiniteAdelicGroupPoints F G)
    (φ : Lp ℂ 2 μ) :
    splitComponentL2InfiniteRightAction F G hi hj hs a φ =
      splitComponentL2RightAction F G hi hj hs (AdelicGroupPoints.ofInfinite F G a) φ :=
  rfl

/-- For split components, every infinite orbit is continuous. -/
theorem continuous_splitComponentL2InfiniteOrbit (φ : Lp ℂ 2 μ) :
    Continuous (fun a : InfiniteAdelicGroupPoints F G =>
      splitComponentL2InfiniteRightAction F G hi hj hs a φ) :=
  continuous_rationalQuotientL2InfiniteOrbit F G hS hi hs.1.2 hs.1.1.1 hInvS φ

/-- For split components, `splitComponentL2Equiv` carries the published positive-torus infinite
action, for any splitting coordinates of `T`, to `splitComponentL2InfiniteRightAction`. -/
theorem splitComponentL2Equiv_infiniteRightAction (I : Type) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (a : InfiniteAdelicGroupPoints F G)
    (φ : QuotientL2 F G T i (positiveRationalQuotientHaarMeasure F G T i)) :
    splitComponentL2Equiv F G hj hs (haarQuotientL2InfiniteRightAction F G T i hi I e hs.1.2 a φ) =
      splitComponentL2InfiniteRightAction F G hi hj hs a (splitComponentL2Equiv F G hj hs φ) :=
  quotientL2Equiv_infiniteRightAction F G hS hi hs.1.2 hInvS I e a φ

variable (K : OpenSubgroup (FiniteAdelicGroupPoints F G)) [CompactSpace K]

attribute [local instance] finiteAverageTopologicalGroup finiteAverageSecondCountable
  finiteAverageMeasurableSpace finiteAverageBorelSpace

/-- For split components, averaging over a compact open subgroup intertwines the infinite
action. -/
theorem splitComponentL2FiniteAverage_infiniteRightAction (a : InfiniteAdelicGroupPoints F G)
    (φ : Lp ℂ 2 μ) :
    splitComponentL2InfiniteRightAction F G hi hj hs a
        (splitComponentL2FiniteAverage F G hi K hj hs φ) =
      splitComponentL2FiniteAverage F G hi K hj hs
        (splitComponentL2InfiniteRightAction F G hi hj hs a φ) :=
  rationalQuotientL2FiniteAverage_infiniteRightAction F G hS hi hs.1.2 hs.1.1.1 hInvS K a φ

end SplitComponents

end Langlands.Global.RestrictionSplitCentre
