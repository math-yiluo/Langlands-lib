import Langlands.AllFieldBZ.Group.GL.CompactOpen
import Langlands.AllFieldBZ.Group.GL.MirabolicMixedOrbitRadicals
import Langlands.AllFieldBZ.Group.GL.MirabolicMixedOrbitSectionCoefficients
import Langlands.AllFieldBZ.Group.GL.MirabolicMixedOrbitStages
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicCharacter
import Langlands.AllFieldBZ.Representation.Induction.SplitStagesCharacterIntegrand
import Langlands.AllFieldBZ.Representation.Mirabolic.MixedProducts
import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiStagesComparison

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiStagesComparison`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiStagesComparison` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
open Langlands.Derivative.MirabolicProductMinus hiding padic_leftPhiStagesCharacterEquiv padic_leftPhiStagesCharacterEquiv_natural plusKernelSmoothTheta
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.AllFieldBZ.GeneralLinear.Mirabolic
open Langlands.GeneralLinear.Mirabolic.MixedOrbit hiding isTopologicalRing_of_topologicalData
open Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit
open Langlands.Induction
open Langlands.Induction.SplitKernelLocalization
open MeasureTheory
open MeasureTheory.Measure
open Langlands.QuotientIntegration
open Langlands.HarmonicAnalysis
open Topology
universe uF uV uW

section KernelTopology
variable {R : Type uF} [CommRing R] [TopologicalSpace R]

end KernelTopology
private theorem _root_.Langlands.Derivative.MirabolicProductMinus.measureRightOfComm {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) [IsMulLeftInvariant μ] (hcomm : ∀ a b : G, a * b = b * a) :
    IsMulRightInvariant μ where
  map_mul_right_eq_self g := by
    rw [show (fun x : G => x * g) = (fun x => g * x) from funext (fun x => hcomm x g)]
    exact map_mul_left_eq_self μ g

section ActualMeasures
variable {R : Type uF} [CommRing R] [TopologicalSpace R]
  [IsTopologicalRing R] [T2Space R] (k r : ℕ) (i : Fin 2)
variable [LocallyCompactSpace (GeneralLinear (k + r + 3) R)]

local notation "rP" => leftPhiStagesRetraction k r (R := R) i
local notation "HP" => leftPhiStagesStabilizer k r (R := R) i
local notation "I" => Subgroup.comap (Subgroup.subtype (MonoidHom.ker rP)) HP

local instance stagesKernelLocallyCompact : LocallyCompactSpace (rP).ker :=
  leftPhiHaar_kernel_locallyCompact k r i
local instance stagesKernelMeasurable : MeasurableSpace (rP).ker := borel _
local instance stagesKernelBorel : BorelSpace (rP).ker := ⟨rfl⟩
local instance stagesIntersectionMeasurable : MeasurableSpace I := borel _
local instance stagesIntersectionBorel : BorelSpace I := ⟨rfl⟩
local instance stagesQuotientMeasurable : MeasurableSpace (QuotientIntegration.LeftQuotient I) := borel _
local instance stagesQuotientBorel : BorelSpace (QuotientIntegration.LeftQuotient I) := ⟨rfl⟩
local instance stagesIntersectionLocallyCompact : LocallyCompactSpace I :=
  ((leftPhiHaar_stabilizer_isClosed k r i).preimage continuous_subtype_val).locallyCompactSpace

local instance stagesKernelHaarRight : IsMulRightInvariant (haar : Measure (rP).ker) :=
  measureRightOfComm haar (leftPhiStagesKernelCommGroup k r i).mul_comm
local instance stagesIntersectionHaarRight : IsMulRightInvariant (haar : Measure I) :=
  measureRightOfComm haar (fun a b => Subtype.ext
    ((leftPhiStagesKernelCommGroup k r i).mul_comm a.val b.val))

section Comparison
variable [NonarchimedeanGroup (GeneralLinear (k + r + 3) R)]
variable (ψ : UnitaryAdditiveCharacter R)
variable (hψ : IsOpen ((plusKernelTheta ψ (k + r + 1)).ker :
  Set (plusProjection (n := k + r + 1) (F := R)).ker))
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (σ : Representation ℂ (leftStabilizer k r R i) V) (hσ : IsSmooth σ)

local notation "p" => plusProjection (n := k + r + 1) (F := R)
local notation "s" => plusSuccessor (n := k + r + 1) (F := R)
local notation "P" => leftStages k r R i
local notation "H" => leftStabilizer k r R i
local notation "K" => Subgroup.comap s P

local instance actualMirabolicLocallyCompact : LocallyCompactSpace (mirabolic (k + r + 2) R) :=
  Mirabolic.locallyCompactSpace
local instance actualPlusLocallyCompact : LocallyCompactSpace (plusSubgroup (k + r + 1) R) :=
  plusSubgroup_isClosed.locallyCompactSpace

omit [IsTopologicalRing R] in
private theorem _root_.Langlands.Derivative.MirabolicProductMinus.actualPlusBasis :
    ∀ O : Set (plusSubgroup (k + r + 1) R), IsOpen O →
      (1 : plusSubgroup (k + r + 1) R) ∈ O →
        ∃ U : OpenSubgroup (plusSubgroup (k + r + 1) R),
          IsCompact (U : Set (plusSubgroup (k + r + 1) R)) ∧
            (U : Set (plusSubgroup (k + r + 1) R)) ⊆ O := by
  intro O hO h1
  exact compactOpenSubgroupBasis _ O (hO.mem_nhds h1)

private theorem _root_.Langlands.Derivative.MirabolicProductMinus.actualKernelBasis :
    ∀ O : Set (rP).ker, IsOpen O → (1 : (rP).ker) ∈ O →
      ∃ U : OpenSubgroup (rP).ker, IsCompact (U : Set (rP).ker) ∧
        (U : Set (rP).ker) ⊆ O := by
  intro O hO h1
  exact compactOpenSubgroupBasis _ O (hO.mem_nhds h1)

local notation "θ" => leftPhiComparisonTheta k r ψ hψ
local notation "hθ" => plusKernelTheta_sectionInvariant ψ (k + r + 1)
local notation "hsH" => leftPhiStagesSection_mem k r (R := R) i
local notation "χ" => SplitStagesCharacter.haarCharacter p s plusProjection_plusSuccessor
  P H (leftStages_contains_kernel k r i) (leftStabilizer_isClosed k r R i) hsH
local notation "κ" => SplitStagesCharacter.coefficientAction p s plusProjection_plusSuccessor
  P H (leftStages_contains_kernel k r i) (leftStabilizer_le_stages k r R i)
  (leftStabilizer_isClosed k r R i) hsH θ hθ σ

variable {τ : Representation ℂ (leftStabilizer k r R i) W} (hτ : IsSmooth τ)

end Comparison
end ActualMeasures
section Padic
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)
variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The positive character on the actual plus kernel is smooth for the supplied topology. -/
def plusKernelSmoothTheta (n : ℕ) :
    letI := T.topology
    SmoothCharacter ℂ (plusProjection (n := n) (F := F.Carrier)).ker := by
  let := T.topology
  exact {
    toMonoidHom := plusKernelTheta ψ n
    isOpen_ker := (T.mirabolicTheta_isOpen_ker ψ n).preimage
      (plusKernelRadicalContinuousEquiv (R := F.Carrier) n).continuous }

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The actual stages comparison, deriving all topology and Haar data from the
supplied p-adic realization. -/
def padic_leftPhiStagesCharacterEquiv (k r : ℕ) (i : Fin 2)
    (σ : Representation ℂ (leftStabilizer k r F.Carrier i) V)
    (hσ : letI := T.topology; IsSmooth σ) :
    letI := T.topology
    letI := T.fieldT2
    letI := Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit.isTopologicalRing_of_topologicalData F T
    (localizedAction
      (plusProjection (n := k + r + 1) (F := F.Carrier))
      (plusSuccessor (n := k + r + 1) (F := F.Carrier))
      (plusKernelTheta ψ (k + r + 1))
      (plusKernelTheta_sectionInvariant ψ (k + r + 1))
      (compactInduced (leftStabilizer k r F.Carrier i) σ)).Equiv
        (compactInduced
          (Subgroup.comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))
            (leftStages k r F.Carrier i))
          (leftPhiStagesAction k r ψ i σ)) := by
  let := T.topology
  let := T.fieldT2
  let := Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit.isTopologicalRing_of_topologicalData F T
  let := T.generalLinearLocallyCompactSpace (k + r + 3)
  let := T.generalLinearNonarchimedean (k + r + 3)
  exact leftPhiStagesCharacterEquiv k r i ψ
    (plusKernelSmoothTheta T ψ (k + r + 1)).isOpen_ker σ hσ

set_option maxHeartbeats 800000 in
/-- Supplied-topology comparison is natural on the complete localization, with
independent coefficient carrier universes. -/
theorem padic_leftPhiStagesCharacterEquiv_natural (k r : ℕ) (i : Fin 2)
    {σ : Representation ℂ (leftStabilizer k r F.Carrier i) V}
    {τ : Representation ℂ (leftStabilizer k r F.Carrier i) W}
    (hσ : letI := T.topology; IsSmooth σ)
    (hτ : letI := T.topology; IsSmooth τ)
    (f : σ.IntertwiningMap τ)
    (z : letI := T.topology
      letI := T.fieldT2
      letI := Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit.isTopologicalRing_of_topologicalData F T
      Jacquet.Localization.Coinvariants
      (compactInduced (leftStabilizer k r F.Carrier i) σ)
      (plusProjection (n := k + r + 1) (F := F.Carrier)).ker
      (plusKernelTheta ψ (k + r + 1))) :
    letI := T.topology
    letI := T.fieldT2
    letI := Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit.isTopologicalRing_of_topologicalData F T
    padic_leftPhiStagesCharacterEquiv T ψ k r i τ hτ
        (sectionMap
          (plusProjection (n := k + r + 1) (F := F.Carrier))
          (plusSuccessor (n := k + r + 1) (F := F.Carrier))
          (plusKernelTheta ψ (k + r + 1))
          (plusKernelTheta_sectionInvariant ψ (k + r + 1))
          (compactInducedMap (leftStabilizer k r F.Carrier i) f) z) =
      compactInducedMap
        (Subgroup.comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))
          (leftStages k r F.Carrier i))
        (leftPhiStagesMap k r ψ i f)
        (padic_leftPhiStagesCharacterEquiv T ψ k r i σ hσ z) := by
  let := T.topology
  let := T.fieldT2
  let := Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit.isTopologicalRing_of_topologicalData F T
  let := T.generalLinearLocallyCompactSpace (k + r + 3)
  let := T.generalLinearNonarchimedean (k + r + 3)
  exact leftPhiStagesCharacterEquiv_natural k r i ψ
    (plusKernelSmoothTheta T ψ (k + r + 1)).isOpen_ker σ hσ hτ f z

end Padic
end Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
