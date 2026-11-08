import Langlands.Automorphic.GroupSchemeFullAEL2FiniteAverage
import Langlands.Automorphic.GroupSchemeQuotientL2InfiniteAction

/-! # The original infinite adelic action on the full all-parabolic AE cusp L2 space -/

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
  (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

local notation "μQ" => positiveRationalQuotientHaarMeasure F G T i
local notation "S" => fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
local notation "ρ" => fullAEL2CuspidalRightAction F G hPD hG T i hi I e hc
local notation "πc" => fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc

/-- Restrict the unchanged bounded full cusp action along the actual infinite inclusion. -/
def fullAEL2CuspidalInfiniteRightAction :
    InfiniteAdelicGroupPoints F G →* (S →L[ℂ] S) :=
  (πc).comp (AdelicGroupPoints.ofInfinite F G).toMonoidHom

local notation "π∞" => fullAEL2CuspidalInfiniteRightAction F G hPD hG T i hi I e hc

@[simp]
theorem fullAEL2CuspidalInfiniteRightAction_apply (a : InfiniteAdelicGroupPoints F G)
    (φ : S) :
    π∞ a φ = ρ (AdelicGroupPoints.ofInfinite F G a) φ := rfl

/-- The faithful cusp inclusion carries this action to the original ambient infinite action. -/
theorem fullAEL2CuspidalInfiniteRightAction_val (a : InfiniteAdelicGroupPoints F G)
    (φ : S) :
    (π∞ a φ).val = haarQuotientL2InfiniteRightAction F G T i hi I e hc a φ.val := rfl

theorem norm_fullAEL2CuspidalInfiniteRightAction (a : InfiniteAdelicGroupPoints F G)
    (φ : S) : ‖π∞ a φ‖ = ‖φ‖ :=
  norm_fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc _ φ

/-- Every original infinite cusp orbit is continuous for the original point topology. -/
theorem continuous_fullAEL2CuspidalInfiniteOrbit (φ : S) :
    Continuous (fun a : InfiniteAdelicGroupPoints F G => π∞ a φ) :=
  (fullAEL2CuspidalOrbitMap F G hPD hG T i hi I e hc φ).continuous.comp
    (AdelicGroupPoints.ofInfinite F G).continuous

/-- Original infinite cusp orbits are AE strongly measurable for every supplied measure. -/
theorem fullAEL2CuspidalInfiniteOrbit_aestronglyMeasurable
    (ν : Measure (InfiniteAdelicGroupPoints F G)) (φ : S) :
    AEStronglyMeasurable (fun a : InfiniteAdelicGroupPoints F G => π∞ a φ) ν :=
  (continuous_fullAEL2CuspidalInfiniteOrbit F G hPD hG T i hi I e hc φ).stronglyMeasurable.aestronglyMeasurable

/-- The actual original finite and infinite cusp actions commute. -/
theorem fullAEL2CuspidalInfiniteFinite_commute (a : InfiniteAdelicGroupPoints F G)
    (b : FiniteAdelicGroupPoints F G) (φ : S) :
    π∞ a (fullAEL2CuspidalFiniteRightAction F G hPD hG T i hi I e hc b φ) =
      fullAEL2CuspidalFiniteRightAction F G hPD hG T i hi I e hc b (π∞ a φ) := by
  change πc (AdelicGroupPoints.ofInfinite F G a)
      (πc (AdelicGroupPoints.ofFinite F G b) φ) =
    πc (AdelicGroupPoints.ofFinite F G b) (πc (AdelicGroupPoints.ofInfinite F G a) φ)
  exact congrArg (fun A : S →L[ℂ] S => A φ)
    ((AdelicGroupPoints.factors_commute F G a b).map πc).eq

/-- The original subtype-valued orthogonal projection intertwines the infinite actions. -/
theorem fullAEL2CuspidalOrthogonalProjection_infiniteRightAction
    (a : InfiniteAdelicGroupPoints F G) (φ : Lp ℂ 2 μQ) :
    fullAEL2CuspidalOrthogonalProjection F G hPD hG T i hi I e hc
      (haarQuotientL2InfiniteRightAction F G T i hi I e hc a φ) =
        π∞ a (fullAEL2CuspidalOrthogonalProjection F G hPD hG T i hi I e hc φ) :=
  fullAEL2CuspidalOrthogonalProjection_rightAction F G hPD hG T i hi I e hc
    (AdelicGroupPoints.ofInfinite F G a) φ

/-- The original ambient cusp projection commutes with the ambient infinite action. -/
theorem fullAEL2CuspidalAmbientProjection_infiniteRightAction
    (a : InfiniteAdelicGroupPoints F G) (φ : Lp ℂ 2 μQ) :
    fullAEL2CuspidalAmbientProjection F G hPD hG T i hi I e hc
      (haarQuotientL2InfiniteRightAction F G T i hi I e hc a φ) =
        haarQuotientL2InfiniteRightAction F G T i hi I e hc a
          (fullAEL2CuspidalAmbientProjection F G hPD hG T i hi I e hc φ) :=
  fullAEL2CuspidalAmbientProjection_rightAction F G hPD hG T i hi I e hc
    (AdelicGroupPoints.ofInfinite F G a) φ

variable (K : OpenSubgroup (FiniteAdelicGroupPoints F G)) [CompactSpace K]

local instance fullCuspInfiniteActionKTopologicalGroup : IsTopologicalGroup K :=
  inferInstanceAs (IsTopologicalGroup K.toSubgroup)
local instance fullCuspInfiniteActionKSecondCountable : SecondCountableTopology K :=
  TopologicalSpace.secondCountableTopology_induced _ (FiniteAdelicGroupPoints F G)
    (fun k : K => (k : FiniteAdelicGroupPoints F G))
local instance fullCuspInfiniteActionKMeasurableSpace : MeasurableSpace K := borel K
local instance fullCuspInfiniteActionKBorelSpace : BorelSpace K := ⟨rfl⟩

/-- The constructed finite cusp probability average intertwines the original infinite action. -/
theorem fullAEL2CuspidalFiniteAverage_infiniteRightAction
    (a : InfiniteAdelicGroupPoints F G) (φ : S) :
    π∞ a (fullAEL2CuspidalFiniteAverage F G hPD hG T i hi I e hc K φ) =
      fullAEL2CuspidalFiniteAverage F G hPD hG T i hi I e hc K (π∞ a φ) := by
  exact compactIsometricAverage_intertwiner K
    (fullAEL2CuspidalCompactOpenAction F G hPD hG T i hi I e hc K)
    (norm_fullAEL2CuspidalCompactOpenAction F G hPD hG T i hi I e hc K)
    (continuous_fullAEL2CuspidalCompactOpenOrbit F G hPD hG T i hi I e hc K)
    (fullAEL2CuspidalCompactOpenAction F G hPD hG T i hi I e hc K)
    (norm_fullAEL2CuspidalCompactOpenAction F G hPD hG T i hi I e hc K)
    (continuous_fullAEL2CuspidalCompactOpenOrbit F G hPD hG T i hi I e hc K)
    (π∞ a) (fun k x => fullAEL2CuspidalInfiniteFinite_commute F G hPD hG T i hi I e hc a k x) φ

end Langlands.Automorphic.GroupSchemeFunctions
