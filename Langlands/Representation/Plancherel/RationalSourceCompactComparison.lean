import Langlands.Representation.Plancherel.RationalSourceGammaIndex

/-! # Changing the common compact in the actual source gamma -/

noncomputable section

open MeasureTheory Topology
open scoped ENNReal

namespace Langlands.Haar

universe v

variable {A : Type v} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  [LocallyCompactSpace A] [MeasurableSpace A] [BorelSpace A]

/-- Shrinking the common ambient compact multiplies each original closed
subgroup Haar by its actual finite trace index. -/
theorem subgroupCompactOpenHaar_eq_sourceTraceIndex_smul
    (K H : OpenSubgroup A) (hK : IsCompact (K : Set A))
    (hH : IsCompact (H : Set A)) (L : Subgroup A)
    (hL : IsClosed (L : Set A)) (hHK : H ≤ K) :
    subgroupCompactOpenHaar H hH L hL =
      (sourceTraceIndex K H L : ℝ≥0∞) • subgroupCompactOpenHaar K hK L hL := by
  let μ := subgroupCompactOpenHaar K hK L hL
  let n : ℝ≥0∞ := sourceTraceIndex K H L
  have hn0 : n ≠ 0 := by
    change (sourceTraceIndex K H L : ℝ≥0∞) ≠ 0
    exact_mod_cast sourceTraceIndex_ne_zero K H hK L hL
  have hnt : n ≠ ⊤ := by simp [n]
  have : (n • μ).Regular := Measure.Regular.smul hnt
  apply (compactOpenHaarAlong_eq_of_mass_one H hH L.subtype
    hL.isClosedEmbedding_subtypeVal (n • μ) ?_).symm
  change n * μ {l : L | (l : A) ∈ H} = 1
  rw [subgroupCompactOpenHaar_eq_inv_sourceTraceIndex K H hK L hL hHK]
  exact ENNReal.mul_inv_cancel hn0 hnt

end Langlands.Haar

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalDynamicSource

open Aubert.General Haar HarishChandraSchwartz
open BruhatTits.DynamicUnipotentContainment

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance compactComparisonPointTopology : TopologicalSpace (RationalPoint F G.X) :=
  rationalPointTopology F G.X
local instance compactComparisonPointMeasurable : MeasurableSpace (RationalPoint F G.X) :=
  borel (RationalPoint F G.X)
local instance compactComparisonPointBorel : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
local instance compactComparisonFieldT2 : T2Space F := BruhatTits.localField_t2Space F
local instance compactComparisonPointTopologicalGroup :
    IsTopologicalGroup (RationalPoint F G.X) :=
  rationalPoint_isTopologicalGroup F G
local instance compactComparisonPointT2 : T2Space (RationalPoint F G.X) :=
  rationalPoint_t2Space F G
local instance compactComparisonPointLocallyCompact :
    LocallyCompactSpace (RationalPoint F G.X) :=
  rationalPoint_locallyCompactSpace F G
local instance compactComparisonPointNonarchimedean :
    NonarchimedeanGroup (RationalPoint F G.X) :=
  RationalPointFamily.affineRationalPoint_nonarchimedeanGroup G
local instance compactComparisonFieldSecondCountable : SecondCountableTopology F :=
  localField_secondCountableTopology F
local instance compactComparisonPointSecondCountable :
    SecondCountableTopology (RationalPoint F G.X) :=
  Aubert.General.rationalPoint_secondCountableTopology F G
local instance compactComparisonSubgroupSecondCountable
    (H : Subgroup (RationalPoint F G.X)) :
    SecondCountableTopology H :=
  TopologicalSpace.Subtype.secondCountableTopology (H : Set (RationalPoint F G.X))

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))

local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))
local notation "P" => SubgroupFunctor.carrier (Dynamic.parabolic χ) X₀
local notation "V" => unipotentPoints (oppositeCocharacter χ)

/-- The forced change in gamma when the common compact is shrunk: the
parabolic and opposite-radical Haar indices divided by the ambient index. -/
def gammaCompactIndex (H : OpenSubgroup (RationalPoint F G.X)) : ℝ≥0∞ :=
  (sourceTraceIndex K H P : ℝ≥0∞) *
    (sourceTraceIndex K H V : ℝ≥0∞) *
      (H.toSubgroup.relIndex K.toSubgroup : ℝ≥0∞)⁻¹

/-- Actual gamma at a smaller common compact has precisely the index
change forced by the three original Haar normalizations. -/
theorem gamma_eq_mul_gammaCompactIndex
    (hG : IsConnectedReductive G)
    (H : OpenSubgroup (RationalPoint F G.X))
    (hH : IsCompact (H : Set (RationalPoint F G.X))) (hHK : H ≤ K) :
    gamma χ H hH = gamma χ K hK * gammaCompactIndex χ K H := by
  let : Smooth G.X.hom := hG.smooth
  let : LocallyCompactSpace P := (isClosed_dynamic_parabolic F G χ).locallyCompactSpace
  let : LocallyCompactSpace V :=
    (isClosed_unipotentPoints (oppositeCocharacter χ)).locallyCompactSpace
  have hmeas : MeasurableSet (H.toSubgroup : Set (RationalPoint F G.X)) :=
    H.isOpen.measurableSet
  have hind : Measurable ((H.toSubgroup : Set (RationalPoint F G.X)).indicator
      (1 : RationalPoint F G.X → ℝ≥0∞)) := measurable_one.indicator hmeas
  have hmassK : ambientHaar K hK (K.toSubgroup : Set (RationalPoint F G.X)) = 1 :=
    ambientHaar_self K hK
  have hnull := rationalDynamicOpenCellConull F G hG χ (ambientHaar K hK) inferInstance
  have hglobal := lintegral_eq_openCellConstant_inv_mul_of_rightInvariantOn
    (ambientHaar K hK) (parabolicHaar χ K hK)
    (radicalHaar (oppositeCocharacter χ) K hK)
    (map_mul_right_ambientHaar_of_unipotent K hK (oppositeCocharacter χ))
    (isOpenEmbedding_openCellMap_rationalPoint F G χ) hnull
    K.isOpen.measurableSet
    (by rw [hmassK]; exact one_ne_zero)
    (by rw [hmassK]; exact ENNReal.one_ne_top)
  have hint := hglobal.2.2 _ hind
  simp only [hmassK, one_mul] at hint
  change _ = (gamma χ K hK)⁻¹ * _ at hint
  rw [lintegral_indicator_one hmeas] at hint
  have hswap :
      (∫⁻ p : P, ∫⁻ v : V,
        (H.toSubgroup : Set (RationalPoint F G.X)).indicator 1
          ((p : RationalPoint F G.X) * (v : RationalPoint F G.X)⁻¹)
          ∂(radicalHaar (oppositeCocharacter χ) K hK) ∂(parabolicHaar χ K hK)) =
      openCellConstant (parabolicHaar χ K hK)
        (radicalHaar (oppositeCocharacter χ) K hK) H.toSubgroup := by
    unfold openCellConstant
    rw [lintegral_lintegral_swap]
    exact (hind.comp ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd).inv).measurable).aemeasurable
  rw [hswap] at hint
  have hidx : H.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    let : (H.toSubgroup.subgroupOf K.toSubgroup).FiniteIndex :=
      finiteIndex_subgroupOf_compact_open _ _ hK H.isOpen
    exact Subgroup.FiniteIndex.index_ne_zero
  have hmass : ambientHaar K hK (H.toSubgroup : Set (RationalPoint F G.X)) =
      (H.toSubgroup.relIndex K.toSubgroup : ℝ≥0∞)⁻¹ := by
    exact measure_eq_inv_relIndex (ambientHaar K hK) hHK hmeas hidx
      (ambientHaar_self K hK)
  rw [hmass] at hint
  obtain ⟨hγ0, hγt⟩ := gamma_ne_zero_ne_top_of_smooth K hK χ
  have hcell : openCellConstant (parabolicHaar χ K hK)
      (radicalHaar (oppositeCocharacter χ) K hK) H.toSubgroup =
      gamma χ K hK * (H.toSubgroup.relIndex K.toSubgroup : ℝ≥0∞)⁻¹ := by
    rw [hint, ← mul_assoc, ENNReal.mul_inv_cancel hγ0 hγt, one_mul]
  have hP := subgroupCompactOpenHaar_eq_sourceTraceIndex_smul K H hK hH P
    (isClosed_dynamic_parabolic F G χ) hHK
  have hV := subgroupCompactOpenHaar_eq_sourceTraceIndex_smul K H hK hH V
    (isClosed_unipotentPoints (oppositeCocharacter χ)) hHK
  change parabolicHaar χ H hH = _ at hP
  change radicalHaar (oppositeCocharacter χ) H hH = _ at hV
  change openCellConstant (parabolicHaar χ H hH)
    (radicalHaar (oppositeCocharacter χ) H hH) H.toSubgroup = _
  rw [hP, hV]
  conv_lhs => unfold openCellConstant
  simp only [lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_const_mul' _ _ (by simp)]
  change (sourceTraceIndex K H V : ℝ≥0∞) *
    ((sourceTraceIndex K H P : ℝ≥0∞) *
      openCellConstant (parabolicHaar χ K hK)
        (radicalHaar (oppositeCocharacter χ) K hK) H.toSubgroup) = _
  rw [hcell]
  unfold gammaCompactIndex
  ring

end Langlands.Plancherel.RationalDynamicSource
