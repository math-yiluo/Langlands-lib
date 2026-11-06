import Langlands.Automorphic.GroupSchemeQuotientL2FiniteAverage
import Langlands.Automorphic.GroupSchemeFullAEL2Integrated
import Langlands.Global.AdelicGroupProduct
import Langlands.Global.AdelicGroupPolish
import Langlands.Representation.Unitary.CompactIsometricAverage
import Langlands.Representation.Smooth.Definitions

/-! # Compact open averaging on the original full all-parabolic AE cusp L2 space -/

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

/-- Restrict the unchanged full cusp representation along the actual finite inclusion. -/
def fullAEL2CuspidalFiniteRightAction :
    Representation ℂ (FiniteAdelicGroupPoints F G) (S) :=
  (ρ).comp (AdelicGroupPoints.ofFinite F G).toMonoidHom

@[simp]
theorem fullAEL2CuspidalFiniteRightAction_apply (b : FiniteAdelicGroupPoints F G)
    (φ : S) :
    fullAEL2CuspidalFiniteRightAction F G hPD hG T i hi I e hc b φ =
      ρ (AdelicGroupPoints.ofFinite F G b) φ := rfl

variable (K : OpenSubgroup (FiniteAdelicGroupPoints F G))

/-- The bounded original action restricted to the actual open subgroup. -/
def fullAEL2CuspidalCompactOpenAction : K →* (S →L[ℂ] S) :=
  (fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc).comp
    ((AdelicGroupPoints.ofFinite F G).toMonoidHom.comp K.toSubgroup.subtype)

local notation "πK" => fullAEL2CuspidalCompactOpenAction F G hPD hG T i hi I e hc K

@[simp]
theorem fullAEL2CuspidalCompactOpenAction_apply (k : K) (φ : S) :
    πK k φ = ρ (AdelicGroupPoints.ofFinite F G k) φ := rfl

theorem norm_fullAEL2CuspidalCompactOpenAction (k : K) (φ : S) :
    ‖πK k φ‖ = ‖φ‖ :=
  norm_fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc _ φ

/-- Each original finite orbit restricts continuously to the subgroup topology. -/
theorem continuous_fullAEL2CuspidalCompactOpenOrbit (φ : S) :
    Continuous (fun k : K => πK k φ) :=
  (fullAEL2CuspidalOrbitMap F G hPD hG T i hi I e hc φ).continuous.comp
    ((AdelicGroupPoints.ofFinite F G).continuous.comp continuous_subtype_val)

variable [CompactSpace K]

local instance fullCuspFiniteAverageTopologicalGroup : IsTopologicalGroup K :=
  inferInstanceAs (IsTopologicalGroup K.toSubgroup)
local instance fullCuspFiniteAverageSecondCountable : SecondCountableTopology K :=
  TopologicalSpace.secondCountableTopology_induced _ (FiniteAdelicGroupPoints F G)
    (fun k : K => (k : FiniteAdelicGroupPoints F G))
local instance fullCuspFiniteAverageMeasurableSpace : MeasurableSpace K := borel K
local instance fullCuspFiniteAverageBorelSpace : BorelSpace K := ⟨rfl⟩

local notation "μK" => compactProbabilityHaar K
local notation "hπKnorm" => norm_fullAEL2CuspidalCompactOpenAction F G hPD hG T i hi I e hc K
local notation "hπKcont" => continuous_fullAEL2CuspidalCompactOpenOrbit F G hPD hG T i hi I e hc K

/-- Probability Haar averaging of arbitrary vectors in the original full cusp L2 space. -/
def fullAEL2CuspidalFiniteAverage : S →L[ℂ] S :=
  compactIsometricAverage K πK hπKnorm hπKcont

local notation "P" => fullAEL2CuspidalFiniteAverage F G hPD hG T i hi I e hc K

@[simp]
theorem fullAEL2CuspidalFiniteAverage_apply (φ : S) :
    P φ = ∫ k : K, ρ (AdelicGroupPoints.ofFinite F G k) φ ∂μK :=
  compactIsometricAverage_apply K πK hπKnorm hπKcont φ

/-- Compact Haar averaging is absolutely convergent on every original full cusp vector. -/
theorem fullAEL2CuspidalFiniteAverage_integrable (φ : S) :
    Integrable (fun k : K => ρ (AdelicGroupPoints.ofFinite F G k) φ) μK :=
  compactIsometricOrbit_integrable K πK hπKnorm hπKcont φ

theorem norm_fullAEL2CuspidalFiniteAverage_le : ‖P‖ ≤ 1 :=
  norm_compactIsometricAverage_le K πK hπKnorm hπKcont

/-- Every output is fixed by the original finite action of every element of K. -/
theorem fullAEL2CuspidalFiniteAverage_fixed (k : K) (φ : S) :
    ρ (AdelicGroupPoints.ofFinite F G k) (P φ) = P φ :=
  compactIsometricAverage_fixed K πK hπKnorm hπKcont k φ

/-- The retraction fixes exactly the original K-invariant vectors. -/
theorem fullAEL2CuspidalFiniteAverage_eq_self_iff (φ : S) :
    P φ = φ ↔ ∀ k : K, ρ (AdelicGroupPoints.ofFinite F G k) φ = φ :=
  compactIsometricAverage_eq_self_iff K πK hπKnorm hπKcont φ

theorem fullAEL2CuspidalFiniteAverage_idempotent : (P).comp P = P :=
  compactIsometricAverage_idempotent K πK hπKnorm hπKcont

/-- The output belongs to the existing invariant submodule of the original finite representation. -/
theorem fullAEL2CuspidalFiniteAverage_mem_fixedVectors (φ : S) :
    P φ ∈ Langlands.fixedVectors (fullAEL2CuspidalFiniteRightAction F G hPD hG T i hi I e hc)
      K.toSubgroup :=
  fun k => fullAEL2CuspidalFiniteAverage_fixed F G hPD hG T i hi I e hc K k φ

/-- The constructed output is a smooth vector for the existing finite-action definition. -/
theorem fullAEL2CuspidalFiniteAverage_isSmoothVector (φ : S) :
    Langlands.IsSmoothVector (fullAEL2CuspidalFiniteRightAction F G hPD hG T i hi I e hc) (P φ) :=
  ⟨K, fullAEL2CuspidalFiniteAverage_mem_fixedVectors F G hPD hG T i hi I e hc K φ⟩

/-- The same actual average with codomain in the existing K-invariant submodule. -/
def fullAEL2CuspidalFiniteFixedRetraction :
    S →L[ℂ]
      Langlands.fixedVectors (fullAEL2CuspidalFiniteRightAction F G hPD hG T i hi I e hc)
        K.toSubgroup :=
  (P).codRestrict _ (fullAEL2CuspidalFiniteAverage_mem_fixedVectors F G hPD hG T i hi I e hc K)

@[simp]
theorem fullAEL2CuspidalFiniteFixedRetraction_val (φ : S) :
    (fullAEL2CuspidalFiniteFixedRetraction F G hPD hG T i hi I e hc K φ).val = P φ := rfl

@[simp]
theorem fullAEL2CuspidalFiniteFixedRetraction_inclusion
    (φ : Langlands.fixedVectors (fullAEL2CuspidalFiniteRightAction F G hPD hG T i hi I e hc)
      K.toSubgroup) :
    fullAEL2CuspidalFiniteFixedRetraction F G hPD hG T i hi I e hc K φ.val = φ := by
  apply Subtype.ext
  exact (fullAEL2CuspidalFiniteAverage_eq_self_iff F G hPD hG T i hi I e hc K φ.val).mpr φ.property


local notation "A" => haarQuotientL2FiniteAverage F G T i hi I e hc K
local notation "πA" => haarQuotientL2CompactOpenAction F G T i hi I e hc K
local notation "hπAnorm" => norm_haarQuotientL2CompactOpenAction F G T i hi I e hc K
local notation "hπAcont" => continuous_haarQuotientL2CompactOpenOrbit F G T i hi I e hc K

/-- The faithful original cusp inclusion identifies the two compact subgroup averages. -/
theorem fullAEL2CuspidalFiniteAverage_val (ψ : S) :
    (P ψ).val = A ψ.val := by
  exact compactIsometricAverage_intertwiner K πK hπKnorm hπKcont πA hπAnorm hπAcont
    (fullAEL2CuspidalInclusionLI F G hPD hG T i hi I e hc).toContinuousLinearMap
    (fun _ _ => rfl) ψ

/-- The ambient average preserves all original proper-parabolic cusp conditions. -/
theorem haarQuotientL2FiniteAverage_mem_fullAEL2CuspidalSubmodule
    (φ : Lp ℂ 2 μQ) (hφ : φ ∈ S) : A φ ∈ S := by
  rw [← fullAEL2CuspidalFiniteAverage_val F G hPD hG T i hi I e hc K ⟨φ, hφ⟩]
  exact (P ⟨φ, hφ⟩).property

/-- The same original orthogonal projection intertwines the two finite averages. -/
theorem fullAEL2CuspidalOrthogonalProjection_finiteAverage (φ : Lp ℂ 2 μQ) :
    fullAEL2CuspidalOrthogonalProjection F G hPD hG T i hi I e hc (A φ) =
      P (fullAEL2CuspidalOrthogonalProjection F G hPD hG T i hi I e hc φ) := by
  exact compactIsometricAverage_intertwiner K πA hπAnorm hπAcont πK hπKnorm hπKcont
    (fullAEL2CuspidalOrthogonalProjection F G hPD hG T i hi I e hc)
    (fun k ψ => fullAEL2CuspidalOrthogonalProjection_rightAction F G hPD hG T i hi I e hc
      (AdelicGroupPoints.ofFinite F G k) ψ) φ

/-- The original ambient cusp projection commutes with the finite averaging operator. -/
theorem fullAEL2CuspidalAmbientProjection_finiteAverage (φ : Lp ℂ 2 μQ) :
    fullAEL2CuspidalAmbientProjection F G hPD hG T i hi I e hc (A φ) =
      A (fullAEL2CuspidalAmbientProjection F G hPD hG T i hi I e hc φ) := by
  have h := congrArg (fun ψ : S => ψ.val)
    (fullAEL2CuspidalOrthogonalProjection_finiteAverage F G hPD hG T i hi I e hc K φ)
  exact h.trans (fullAEL2CuspidalFiniteAverage_val F G hPD hG T i hi I e hc K _)

end Langlands.Automorphic.GroupSchemeFunctions
