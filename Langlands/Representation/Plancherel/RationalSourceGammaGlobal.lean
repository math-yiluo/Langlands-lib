import Langlands.Representation.Plancherel.RationalSourceGammaAmbientHaar
import Langlands.Representation.Plancherel.RationalOpenCellConullProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RestrictedOpenCellIntegration

/-! # Global open-cell integration on actual reductive rational points -/

noncomputable section

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

local instance sourceGlobalPointTopology : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
local instance sourceGlobalPointMeasurable : MeasurableSpace (RationalPoint F G.X) := borel (RationalPoint F G.X)
local instance sourceGlobalPointBorel : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
local instance sourceGlobalFieldT2 : T2Space F := BruhatTits.localField_t2Space F
local instance sourceGlobalPointTopologicalGroup : IsTopologicalGroup (RationalPoint F G.X) :=
  rationalPoint_isTopologicalGroup F G
local instance sourceGlobalPointT2 : T2Space (RationalPoint F G.X) := rationalPoint_t2Space F G
local instance sourceGlobalPointLocallyCompact : LocallyCompactSpace (RationalPoint F G.X) :=
  rationalPoint_locallyCompactSpace F G
local instance sourceGlobalPointNonarchimedean : NonarchimedeanGroup (RationalPoint F G.X) :=
  RationalPointFamily.affineRationalPoint_nonarchimedeanGroup G
local instance sourceGlobalFieldSecondCountable : SecondCountableTopology F := localField_secondCountableTopology F
local instance sourceGlobalPointSecondCountable : SecondCountableTopology (RationalPoint F G.X) :=
  Aubert.General.rationalPoint_secondCountableTopology F G
local instance subgroupSecondCountableGlobal (H : Subgroup (RationalPoint F G.X)) :
    SecondCountableTopology H :=
  TopologicalSpace.Subtype.secondCountableTopology (H : Set (RationalPoint F G.X))

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))

local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))
local notation "P" => SubgroupFunctor.carrier (Dynamic.parabolic χ) X₀
local notation "V" => unipotentPoints (oppositeCocharacter χ)

/-- The actual normalized subgroup product pushed through `p * v⁻¹`. -/
def openCellMeasure : Measure (RationalPoint F G.X) :=
  openCellProductPushforward (parabolicHaar χ K hK)
    (radicalHaar (oppositeCocharacter χ) K hK)

/-- Actual conullness and radical right invariance identify the normalized
ambient Haar with the original gamma-scaled product pushforward. -/
theorem ambientHaar_eq_gamma_inv_smul (hG : IsConnectedReductive G) :
    ambientHaar K hK = (gamma χ K hK)⁻¹ • openCellMeasure χ K hK := by
  let : Smooth G.X.hom := hG.smooth
  let : LocallyCompactSpace P := (isClosed_dynamic_parabolic F G χ).locallyCompactSpace
  let : LocallyCompactSpace V :=
    (isClosed_unipotentPoints (oppositeCocharacter χ)).locallyCompactSpace
  have hmass : ambientHaar K hK (K.toSubgroup : Set (RationalPoint F G.X)) = 1 :=
    ambientHaar_self K hK
  have hnull := rationalDynamicOpenCellConull F G hG χ (ambientHaar K hK) inferInstance
  simpa only [hmass, one_mul, gamma, openCellMeasure] using
    measure_eq_openCellConstant_inv_smul_of_rightInvariantOn
      (ambientHaar K hK) (parabolicHaar χ K hK)
      (radicalHaar (oppositeCocharacter χ) K hK)
      (map_mul_right_ambientHaar_of_unipotent K hK (oppositeCocharacter χ))
      (isOpenEmbedding_openCellMap_rationalPoint F G χ) hnull
      K.isOpen.measurableSet
      (by rw [hmass]; exact one_ne_zero)
      (by rw [hmass]; exact ENNReal.one_ne_top)

/-- Global nonnegative integration at the unchanged common-compact scale,
with no supplied conullness or ambient right-invariance premise. -/
theorem lintegral_eq_gamma_inv_mul (hG : IsConnectedReductive G)
    (f : RationalPoint F G.X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ g, f g ∂(ambientHaar K hK)) =
      (gamma χ K hK)⁻¹ *
        ∫⁻ p : P, ∫⁻ v : V,
          f ((p : RationalPoint F G.X) * (v : RationalPoint F G.X)⁻¹)
            ∂(radicalHaar (oppositeCocharacter χ) K hK) ∂(parabolicHaar χ K hK) := by
  let : Smooth G.X.hom := hG.smooth
  let : LocallyCompactSpace P := (isClosed_dynamic_parabolic F G χ).locallyCompactSpace
  let : LocallyCompactSpace V :=
    (isClosed_unipotentPoints (oppositeCocharacter χ)).locallyCompactSpace
  have hmass : ambientHaar K hK (K.toSubgroup : Set (RationalPoint F G.X)) = 1 :=
    ambientHaar_self K hK
  have hnull := rationalDynamicOpenCellConull F G hG χ (ambientHaar K hK) inferInstance
  have ht := lintegral_eq_openCellConstant_inv_mul_of_rightInvariantOn
    (ambientHaar K hK) (parabolicHaar χ K hK)
    (radicalHaar (oppositeCocharacter χ) K hK)
    (map_mul_right_ambientHaar_of_unipotent K hK (oppositeCocharacter χ))
    (isOpenEmbedding_openCellMap_rationalPoint F G χ) hnull
    K.isOpen.measurableSet
    (by rw [hmass]; exact one_ne_zero)
    (by rw [hmass]; exact ENNReal.one_ne_top)
  simpa only [hmass, one_mul, gamma] using ht.2.2 f hf

end Langlands.Plancherel.RationalDynamicSource
