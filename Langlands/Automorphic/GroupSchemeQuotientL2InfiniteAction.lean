import Langlands.Automorphic.GroupSchemeQuotientL2FiniteAverage
import Langlands.Global.InfiniteAdelicModularCharacter

/-! # The original infinite adelic action on canonical quotient L2 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme Langlands.Analysis

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

local notation "μQ" => positiveRationalQuotientHaarMeasure F G T i
local notation "π" => haarQuotientL2BoundedRightAction F G T i hi I e hc

/-- Restrict the unchanged bounded quotient action along the actual infinite inclusion. -/
def haarQuotientL2InfiniteRightAction :
    InfiniteAdelicGroupPoints F G →* (Lp ℂ 2 μQ →L[ℂ] Lp ℂ 2 μQ) :=
  (π).comp (AdelicGroupPoints.ofInfinite F G).toMonoidHom

local notation "π∞" => haarQuotientL2InfiniteRightAction F G T i hi I e hc

@[simp]
theorem haarQuotientL2InfiniteRightAction_apply (a : InfiniteAdelicGroupPoints F G)
    (φ : Lp ℂ 2 μQ) :
    π∞ a φ = π (AdelicGroupPoints.ofInfinite F G a) φ := rfl

theorem norm_haarQuotientL2InfiniteRightAction (a : InfiniteAdelicGroupPoints F G)
    (φ : Lp ℂ 2 μQ) : ‖π∞ a φ‖ = ‖φ‖ :=
  norm_haarQuotientL2BoundedRightAction F G T i hi I e hc _ φ

/-- Every original infinite orbit is continuous for the original point topology. -/
theorem continuous_haarQuotientL2InfiniteOrbit (φ : Lp ℂ 2 μQ) :
    Continuous (fun a : InfiniteAdelicGroupPoints F G => π∞ a φ) :=
  (haarQuotientL2OrbitMap F G T i hi I e hc φ).continuous.comp
    (AdelicGroupPoints.ofInfinite F G).continuous

/-- Original infinite orbits are AE strongly measurable for every supplied measure. -/
theorem haarQuotientL2InfiniteOrbit_aestronglyMeasurable
    (ν : Measure (InfiniteAdelicGroupPoints F G)) (φ : Lp ℂ 2 μQ) :
    AEStronglyMeasurable (fun a : InfiniteAdelicGroupPoints F G => π∞ a φ) ν :=
  (continuous_haarQuotientL2InfiniteOrbit F G T i hi I e hc φ).stronglyMeasurable.aestronglyMeasurable

/-- The actual original finite and infinite quotient actions commute. -/
theorem haarQuotientL2InfiniteFinite_commute (a : InfiniteAdelicGroupPoints F G)
    (b : FiniteAdelicGroupPoints F G) (φ : Lp ℂ 2 μQ) :
    π∞ a (haarQuotientL2FiniteRightAction F G T i hi I e hc b φ) =
      haarQuotientL2FiniteRightAction F G T i hi I e hc b (π∞ a φ) := by
  change π (AdelicGroupPoints.ofInfinite F G a)
      (π (AdelicGroupPoints.ofFinite F G b) φ) =
    π (AdelicGroupPoints.ofFinite F G b) (π (AdelicGroupPoints.ofInfinite F G a) φ)
  exact congrArg (fun A : Lp ℂ 2 μQ →L[ℂ] Lp ℂ 2 μQ => A φ)
    ((AdelicGroupPoints.factors_commute F G a b).map π).eq

variable (K : OpenSubgroup (FiniteAdelicGroupPoints F G)) [CompactSpace K]

local instance infiniteActionKTopologicalGroup : IsTopologicalGroup K :=
  inferInstanceAs (IsTopologicalGroup K.toSubgroup)
local instance infiniteActionKSecondCountable : SecondCountableTopology K :=
  TopologicalSpace.secondCountableTopology_induced _ (FiniteAdelicGroupPoints F G)
    (fun k : K => (k : FiniteAdelicGroupPoints F G))
local instance infiniteActionKMeasurableSpace : MeasurableSpace K := borel K
local instance infiniteActionKBorelSpace : BorelSpace K := ⟨rfl⟩

/-- The constructed finite probability average intertwines the original infinite action. -/
theorem haarQuotientL2FiniteAverage_infiniteRightAction
    (a : InfiniteAdelicGroupPoints F G) (φ : Lp ℂ 2 μQ) :
    π∞ a (haarQuotientL2FiniteAverage F G T i hi I e hc K φ) =
      haarQuotientL2FiniteAverage F G T i hi I e hc K (π∞ a φ) := by
  exact compactIsometricAverage_intertwiner K
    (haarQuotientL2CompactOpenAction F G T i hi I e hc K)
    (norm_haarQuotientL2CompactOpenAction F G T i hi I e hc K)
    (continuous_haarQuotientL2CompactOpenOrbit F G T i hi I e hc K)
    (haarQuotientL2CompactOpenAction F G T i hi I e hc K)
    (norm_haarQuotientL2CompactOpenAction F G T i hi I e hc K)
    (continuous_haarQuotientL2CompactOpenOrbit F G T i hi I e hc K)
    (π∞ a) (fun k x => haarQuotientL2InfiniteFinite_commute F G T i hi I e hc a k x) φ

end Langlands.Automorphic.GroupSchemeFunctions
