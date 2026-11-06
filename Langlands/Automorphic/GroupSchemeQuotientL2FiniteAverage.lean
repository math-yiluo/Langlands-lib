import Langlands.Automorphic.GroupSchemeQuotientL2Integrated
import Langlands.Global.AdelicGroupProduct
import Langlands.Global.AdelicGroupPolish
import Langlands.Representation.Unitary.CompactIsometricAverage
import Langlands.Representation.Smooth.Definitions

/-! # Compact open averaging on the original canonical quotient L2 space -/

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
local notation "hR" => haarQuotientMeasureRightInvariant F G T i hi I e hc
local notation "ρ" => quotientL2RightAction F G T i μQ hR

/-- Restrict the unchanged positive quotient representation along the actual finite inclusion. -/
def haarQuotientL2FiniteRightAction :
    Representation ℂ (FiniteAdelicGroupPoints F G) (Lp ℂ 2 μQ) :=
  (ρ).comp (AdelicGroupPoints.ofFinite F G).toMonoidHom

@[simp]
theorem haarQuotientL2FiniteRightAction_apply (b : FiniteAdelicGroupPoints F G)
    (φ : Lp ℂ 2 μQ) :
    haarQuotientL2FiniteRightAction F G T i hi I e hc b φ =
      ρ (AdelicGroupPoints.ofFinite F G b) φ := rfl

variable (K : OpenSubgroup (FiniteAdelicGroupPoints F G))

/-- The bounded original action restricted to the actual open subgroup. -/
def haarQuotientL2CompactOpenAction : K →* (Lp ℂ 2 μQ →L[ℂ] Lp ℂ 2 μQ) :=
  (haarQuotientL2BoundedRightAction F G T i hi I e hc).comp
    ((AdelicGroupPoints.ofFinite F G).toMonoidHom.comp K.toSubgroup.subtype)

local notation "πK" => haarQuotientL2CompactOpenAction F G T i hi I e hc K

@[simp]
theorem haarQuotientL2CompactOpenAction_apply (k : K) (φ : Lp ℂ 2 μQ) :
    πK k φ = ρ (AdelicGroupPoints.ofFinite F G k) φ := rfl

theorem norm_haarQuotientL2CompactOpenAction (k : K) (φ : Lp ℂ 2 μQ) :
    ‖πK k φ‖ = ‖φ‖ :=
  norm_haarQuotientL2BoundedRightAction F G T i hi I e hc _ φ

/-- Each original finite orbit restricts continuously to the subgroup topology. -/
theorem continuous_haarQuotientL2CompactOpenOrbit (φ : Lp ℂ 2 μQ) :
    Continuous (fun k : K => πK k φ) :=
  (haarQuotientL2OrbitMap F G T i hi I e hc φ).continuous.comp
    ((AdelicGroupPoints.ofFinite F G).continuous.comp continuous_subtype_val)

variable [CompactSpace K]

local instance finiteAverageTopologicalGroup : IsTopologicalGroup K :=
  inferInstanceAs (IsTopologicalGroup K.toSubgroup)
local instance finiteAverageSecondCountable : SecondCountableTopology K :=
  TopologicalSpace.secondCountableTopology_induced _ (FiniteAdelicGroupPoints F G)
    (fun k : K => (k : FiniteAdelicGroupPoints F G))
local instance finiteAverageMeasurableSpace : MeasurableSpace K := borel K
local instance finiteAverageBorelSpace : BorelSpace K := ⟨rfl⟩

local notation "μK" => compactProbabilityHaar K
local notation "hπKnorm" => norm_haarQuotientL2CompactOpenAction F G T i hi I e hc K
local notation "hπKcont" => continuous_haarQuotientL2CompactOpenOrbit F G T i hi I e hc K

/-- Probability Haar averaging of arbitrary vectors in the original quotient L2 space. -/
def haarQuotientL2FiniteAverage : Lp ℂ 2 μQ →L[ℂ] Lp ℂ 2 μQ :=
  compactIsometricAverage K πK hπKnorm hπKcont

local notation "P" => haarQuotientL2FiniteAverage F G T i hi I e hc K

@[simp]
theorem haarQuotientL2FiniteAverage_apply (φ : Lp ℂ 2 μQ) :
    P φ = ∫ k : K, ρ (AdelicGroupPoints.ofFinite F G k) φ ∂μK :=
  compactIsometricAverage_apply K πK hπKnorm hπKcont φ

/-- Compact Haar averaging is absolutely convergent on every original null class. -/
theorem haarQuotientL2FiniteAverage_integrable (φ : Lp ℂ 2 μQ) :
    Integrable (fun k : K => ρ (AdelicGroupPoints.ofFinite F G k) φ) μK :=
  compactIsometricOrbit_integrable K πK hπKnorm hπKcont φ

theorem norm_haarQuotientL2FiniteAverage_le : ‖P‖ ≤ 1 :=
  norm_compactIsometricAverage_le K πK hπKnorm hπKcont

/-- Every output is fixed by the original finite action of every element of K. -/
theorem haarQuotientL2FiniteAverage_fixed (k : K) (φ : Lp ℂ 2 μQ) :
    ρ (AdelicGroupPoints.ofFinite F G k) (P φ) = P φ :=
  compactIsometricAverage_fixed K πK hπKnorm hπKcont k φ

/-- The retraction fixes exactly the original K-invariant vectors. -/
theorem haarQuotientL2FiniteAverage_eq_self_iff (φ : Lp ℂ 2 μQ) :
    P φ = φ ↔ ∀ k : K, ρ (AdelicGroupPoints.ofFinite F G k) φ = φ :=
  compactIsometricAverage_eq_self_iff K πK hπKnorm hπKcont φ

theorem haarQuotientL2FiniteAverage_idempotent : (P).comp P = P :=
  compactIsometricAverage_idempotent K πK hπKnorm hπKcont

/-- The output belongs to the existing invariant submodule of the original finite representation. -/
theorem haarQuotientL2FiniteAverage_mem_fixedVectors (φ : Lp ℂ 2 μQ) :
    P φ ∈ Langlands.fixedVectors (haarQuotientL2FiniteRightAction F G T i hi I e hc)
      K.toSubgroup :=
  fun k => haarQuotientL2FiniteAverage_fixed F G T i hi I e hc K k φ

/-- The constructed output is a smooth vector for the existing finite-action definition. -/
theorem haarQuotientL2FiniteAverage_isSmoothVector (φ : Lp ℂ 2 μQ) :
    Langlands.IsSmoothVector (haarQuotientL2FiniteRightAction F G T i hi I e hc) (P φ) :=
  ⟨K, haarQuotientL2FiniteAverage_mem_fixedVectors F G T i hi I e hc K φ⟩

/-- The same actual average with codomain in the existing K-invariant submodule. -/
def haarQuotientL2FiniteFixedRetraction :
    Lp ℂ 2 μQ →L[ℂ]
      Langlands.fixedVectors (haarQuotientL2FiniteRightAction F G T i hi I e hc)
        K.toSubgroup :=
  (P).codRestrict _ (haarQuotientL2FiniteAverage_mem_fixedVectors F G T i hi I e hc K)

@[simp]
theorem haarQuotientL2FiniteFixedRetraction_val (φ : Lp ℂ 2 μQ) :
    (haarQuotientL2FiniteFixedRetraction F G T i hi I e hc K φ).val = P φ := rfl

@[simp]
theorem haarQuotientL2FiniteFixedRetraction_inclusion
    (φ : Langlands.fixedVectors (haarQuotientL2FiniteRightAction F G T i hi I e hc)
      K.toSubgroup) :
    haarQuotientL2FiniteFixedRetraction F G T i hi I e hc K φ.val = φ := by
  apply Subtype.ext
  exact (haarQuotientL2FiniteAverage_eq_self_iff F G T i hi I e hc K φ.val).mpr φ.property

end Langlands.Automorphic.GroupSchemeFunctions
