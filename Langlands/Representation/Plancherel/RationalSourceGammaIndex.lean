import Langlands.Representation.Plancherel.RationalSourceOpenCellCoordinates
import Langlands.Analysis.Local.CompactOpenIndexHaarProof

/-! # The actual source gamma from compact-open subgroup indices -/

noncomputable section

open MeasureTheory Topology
open scoped ENNReal

namespace Langlands.Haar

universe v

variable {A : Type v} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]

/-- The finite relative index of two ambient compact-open traces on an
actual subgroup. The definition itself does not assume finiteness. -/
def sourceTraceIndex (K H : OpenSubgroup A) (L : Subgroup A) : ℕ :=
  (H.toSubgroup.comap L.subtype).relIndex (K.toSubgroup.comap L.subtype)

/-- Openness of the smaller trace and compactness of the larger trace
prove that the relative index is finite, hence nonzero. -/
theorem sourceTraceIndex_ne_zero (K H : OpenSubgroup A)
    (hK : IsCompact (K : Set A)) (L : Subgroup A) (hL : IsClosed (L : Set A)) :
    sourceTraceIndex K H L ≠ 0 := by
  have : ((H.toSubgroup.comap L.subtype).subgroupOf
      (K.toSubgroup.comap L.subtype)).FiniteIndex :=
    finiteIndex_subgroupOf_compact_open _ _
      (hL.isClosedEmbedding_subtypeVal.isCompact_preimage hK)
      (H.isOpen.preimage continuous_subtype_val)
  exact Subgroup.FiniteIndex.index_ne_zero

variable [MeasurableSpace A] [BorelSpace A]

/-- The prescribed source Haar evaluates a smaller open trace as the
inverse of its actual relative index. -/
theorem subgroupCompactOpenHaar_eq_inv_sourceTraceIndex
    (K H : OpenSubgroup A) (hK : IsCompact (K : Set A))
    (L : Subgroup A) (hL : IsClosed (L : Set A)) (hHK : H ≤ K) :
    subgroupCompactOpenHaar K hK L hL {l : L | (l : A) ∈ H} =
      (sourceTraceIndex K H L : ℝ≥0∞)⁻¹ := by
  change subgroupCompactOpenHaar K hK L hL
    (H.toSubgroup.comap L.subtype : Set L) = _
  apply HarishChandraSchwartz.measure_eq_inv_relIndex
    (subgroupCompactOpenHaar K hK L hL)
    (Z := H.toSubgroup.comap L.subtype) (Y := K.toSubgroup.comap L.subtype)
  · exact fun _ hx => hHK hx
  · exact (H.isOpen.preimage continuous_subtype_val).measurableSet
  · exact sourceTraceIndex_ne_zero K H hK L hL
  · exact subgroupCompactOpenHaar_mass K hK L hL

end Langlands.Haar

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalDynamicSource

open Aubert.General Haar HarishChandraSchwartz
open BruhatTits.DynamicUnipotentContainment

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance sourceGammaIndexPointTopology : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
local instance sourceGammaIndexPointMeasurable : MeasurableSpace (RationalPoint F G.X) := borel (RationalPoint F G.X)
local instance sourceGammaIndexPointBorel : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
local instance sourceGammaIndexFieldT2 : T2Space F := BruhatTits.localField_t2Space F
local instance sourceGammaIndexPointTopologicalGroup : IsTopologicalGroup (RationalPoint F G.X) :=
  rationalPoint_isTopologicalGroup F G
local instance sourceGammaIndexPointT2 : T2Space (RationalPoint F G.X) := rationalPoint_t2Space F G
local instance sourceGammaIndexPointLocallyCompact : LocallyCompactSpace (RationalPoint F G.X) :=
  rationalPoint_locallyCompactSpace F G
local instance sourceGammaIndexPointNonarchimedean : NonarchimedeanGroup (RationalPoint F G.X) :=
  RationalPointFamily.affineRationalPoint_nonarchimedeanGroup G
local instance sourceGammaIndexFieldSecondCountable : SecondCountableTopology F := localField_secondCountableTopology F
local instance sourceGammaIndexPointSecondCountable : SecondCountableTopology (RationalPoint F G.X) :=
  Aubert.General.rationalPoint_secondCountableTopology F G
local instance subgroupSecondCountableGammaIndex (H : Subgroup (RationalPoint F G.X)) :
    SecondCountableTopology H :=
  TopologicalSpace.Subtype.secondCountableTopology (H : Set (RationalPoint F G.X))

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))
local notation "P" => SubgroupFunctor.carrier (Dynamic.parabolic χ) X₀
local notation "M" => SubgroupFunctor.carrier (Dynamic.centralizer χ) X₀
local notation "U" => unipotentPoints χ
local notation "V" => unipotentPoints (oppositeCocharacter χ)

/-- The original common-compact gamma expressed using actual subgroup
indices, before imposing the local factorization that identifies it. -/
def gammaIndex (K H : OpenSubgroup (RationalPoint F G.X)) : ℝ≥0∞ :=
  (H.toSubgroup.relIndex K.toSubgroup : ℝ≥0∞) *
    ((sourceTraceIndex K H M : ℝ≥0∞)⁻¹ *
      ((sourceTraceIndex K H U : ℝ≥0∞)⁻¹ *
        (sourceTraceIndex K H V : ℝ≥0∞)⁻¹))

variable (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))

/-- Evaluating the actual global coordinate formula on the indicator of
an open subgroup gives its original Haar mass, without ambient right
invariance or a new scalar normalization. -/
theorem ambientHaar_eq_gamma_inv_mul_traces
    (hG : IsConnectedReductive G)
    (hstable : ∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K)
    (H : OpenSubgroup (RationalPoint F G.X))
    (hfactor : ∀ (m : M) (u : U) (v : V),
      (m : RationalPoint F G.X) * u * (v : RationalPoint F G.X) ∈ H ↔
        (m : RationalPoint F G.X) ∈ H ∧
          (u : RationalPoint F G.X) ∈ H ∧ (v : RationalPoint F G.X) ∈ H) :
    ambientHaar K hK (H : Set (RationalPoint F G.X)) =
      (gamma χ K hK)⁻¹ *
        (leviHaar χ K hK {m : M | (m : RationalPoint F G.X) ∈ H} *
          (radicalHaar χ K hK {u : U | (u : RationalPoint F G.X) ∈ H} *
            radicalHaar (oppositeCocharacter χ) K hK
              {v : V | (v : RationalPoint F G.X) ∈ H})) := by
  have hH := H.isOpen.measurableSet
  have hm : Measurable ((H : Set (RationalPoint F G.X)).indicator
      (1 : RationalPoint F G.X → ℝ≥0∞)) := measurable_one.indicator hH
  have h := lintegral_eq_levi_radical_of_limit_stable χ K hK hG hstable _ hm
  rw [lintegral_indicator_one hH] at h
  rw [h]
  congr 1
  have hMH : MeasurableSet {m : M | (m : RationalPoint F G.X) ∈ H} :=
    measurable_subtype_coe hH
  have hUH : MeasurableSet {u : U | (u : RationalPoint F G.X) ∈ H} :=
    measurable_subtype_coe hH
  have hVH : MeasurableSet {v : V | (v : RationalPoint F G.X) ∈ H} :=
    measurable_subtype_coe hH
  have hpt (m : M) (u : U) (v : V) :
      (H : Set (RationalPoint F G.X)).indicator (1 : RationalPoint F G.X → ℝ≥0∞)
          ((m : RationalPoint F G.X) * u * (v : RationalPoint F G.X)) =
        {m : M | (m : RationalPoint F G.X) ∈ H}.indicator 1 m *
          ({u : U | (u : RationalPoint F G.X) ∈ H}.indicator 1 u *
            {v : V | (v : RationalPoint F G.X) ∈ H}.indicator 1 v) := by
    by_cases hmH : (m : RationalPoint F G.X) ∈ H <;>
      by_cases huH : (u : RationalPoint F G.X) ∈ H <;>
        by_cases hvH : (v : RationalPoint F G.X) ∈ H <;>
          simp [Set.indicator, hfactor, hmH, huH, hvH]
  set A : M → ℝ≥0∞ := {m : M | (m : RationalPoint F G.X) ∈ H}.indicator 1
  set B : U → ℝ≥0∞ := {u : U | (u : RationalPoint F G.X) ∈ H}.indicator 1
  set C : V → ℝ≥0∞ := {v : V | (v : RationalPoint F G.X) ∈ H}.indicator 1
  have hA : Measurable A := measurable_one.indicator hMH
  have hB : Measurable B := measurable_one.indicator hUH
  have hC : Measurable C := measurable_one.indicator hVH
  calc
    _ = ∫⁻ m : M, ∫⁻ u : U, A m *
        (B u * radicalHaar (oppositeCocharacter χ) K hK
          {v : V | (v : RationalPoint F G.X) ∈ H})
          ∂(radicalHaar χ K hK) ∂(leviHaar χ K hK) := by
      refine lintegral_congr fun m => lintegral_congr fun u => ?_
      simp_rw [hpt]
      rw [lintegral_const_mul _ (hC.const_mul _), lintegral_const_mul _ hC,
        lintegral_indicator_one hVH]
    _ = ∫⁻ m : M, A m *
        (radicalHaar χ K hK {u : U | (u : RationalPoint F G.X) ∈ H} *
          radicalHaar (oppositeCocharacter χ) K hK
            {v : V | (v : RationalPoint F G.X) ∈ H}) ∂(leviHaar χ K hK) := by
      refine lintegral_congr fun m => ?_
      rw [lintegral_const_mul _ (hB.mul_const _), lintegral_mul_const _ hB,
        lintegral_indicator_one hUH]
    _ = _ := by
      rw [lintegral_mul_const _ hA, lintegral_indicator_one hMH]

/-- The local open-cell factorization expresses the original gamma as a
product of actual finite subgroup indices. Only the compact-limit and
local factorization premises remain; no right-invariance input is used. -/
theorem gamma_eq_gammaIndex
    (hG : IsConnectedReductive G)
    (hstable : ∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K)
    (H : OpenSubgroup (RationalPoint F G.X)) (hHK : H ≤ K)
    (hfactor : ∀ (m : M) (u : U) (v : V),
      (m : RationalPoint F G.X) * u * (v : RationalPoint F G.X) ∈ H ↔
        (m : RationalPoint F G.X) ∈ H ∧
          (u : RationalPoint F G.X) ∈ H ∧ (v : RationalPoint F G.X) ∈ H) :
    gamma χ K hK = gammaIndex χ K H := by
  let : Smooth G.X.hom := hG.smooth
  have hfin : H.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    have : (H.toSubgroup.subgroupOf K.toSubgroup).FiniteIndex :=
      finiteIndex_subgroupOf_compact_open K.toSubgroup H.toSubgroup hK H.isOpen
    exact Subgroup.FiniteIndex.index_ne_zero
  have hvol := ambientHaar_eq_gamma_inv_mul_traces χ K hK hG hstable H hfactor
  have hmass : ambientHaar K hK (K.toSubgroup : Set (RationalPoint F G.X)) = 1 :=
    ambientHaar_self K hK
  have hindex := measure_eq_relIndex_mul (ambientHaar K hK) hHK
    H.isOpen.measurableSet hfin
  change ambientHaar K hK (K : Set (RationalPoint F G.X)) =
    (H.toSubgroup.relIndex K.toSubgroup : ℝ≥0∞) *
      ambientHaar K hK (H : Set (RationalPoint F G.X)) at hindex
  have hM := subgroupCompactOpenHaar_eq_inv_sourceTraceIndex K H hK M
    (isClosed_levi χ) hHK
  have hU := subgroupCompactOpenHaar_eq_inv_sourceTraceIndex K H hK U
    (isClosed_unipotentPoints χ) hHK
  have hV := subgroupCompactOpenHaar_eq_inv_sourceTraceIndex K H hK V
    (isClosed_unipotentPoints (oppositeCocharacter χ)) hHK
  change ambientHaar K hK (H : Set (RationalPoint F G.X)) =
    (gamma χ K hK)⁻¹ * _ at hvol
  rw [hM, hU, hV] at hvol
  have hproduct : 1 = (gamma χ K hK)⁻¹ * gammaIndex χ K H := by
    calc
      1 = (H.toSubgroup.relIndex K.toSubgroup : ℝ≥0∞) *
          ambientHaar K hK (H : Set (RationalPoint F G.X)) := by
        simpa only [ambientHaar_self] using hindex
      _ = _ := by rw [hvol]; unfold gammaIndex; ring
  obtain ⟨hγ0, hγtop⟩ := gamma_ne_zero_ne_top_of_smooth K hK χ
  calc
    gamma χ K hK = gamma χ K hK * 1 := (mul_one _).symm
    _ = gamma χ K hK * ((gamma χ K hK)⁻¹ * gammaIndex χ K H) := by rw [hproduct]
    _ = gammaIndex χ K H := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hγ0 hγtop, one_mul]

end Langlands.Plancherel.RationalDynamicSource
