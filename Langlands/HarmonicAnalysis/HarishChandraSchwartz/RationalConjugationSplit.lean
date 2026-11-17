import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalSplit
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OpenCellPoints
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConjugationPairing
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiSquareIntegrable
import Langlands.Representation.Plancherel.RationalDynamicSourceHaar
import Langlands.Representation.Plancherel.RationalOpenCellConullProof
import Langlands.Representation.Plancherel.RationalSourceOpenCellCoordinates
import Langlands.Representation.Aubert.General.RationalOppositeParabolic
import Langlands.Representation.Unitary.CentralQuotientForm

/-! # The actual conjugation integral split on a truncated open cell

The truncated cell is an open image of its explicit Levi/radical coordinates.
The actual rational-point homeomorphism and conullness theorems discharge
the geometric assumptions of the generic complex-integral splitting theorem.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

section Cell

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {M U P V : Subgroup Γ}
  (hMU : M ≤ Subgroup.normalizer (U : Set Γ))

/-- The cell whose coordinates satisfy the two truncation conditions in
the proof of VIII.3.1. -/
def conjugationTruncatedCell (A : Set Γ) (B : Set V) (a : M) : Set Γ :=
  openCellCoord '' {x : (M × U) × V |
    (a : Γ) * (conjUnipotent hMU x.1.1 x.1.2 : Γ) * (a : Γ)⁻¹ ∈ A ∧ x.2 ∈ B}

variable (hP : ∀ x : M × U, leviUnipotentMul x ∈ P)
  (hhomeo : IsHomeomorph (leviUnipotentCoord hP))
  (hcell : IsOpenEmbedding (openCellMap (P := P) (V := V)))

include hhomeo hcell

omit [IsTopologicalGroup Γ] in
/-- The complete Levi/radical coordinates form an open embedding. -/
theorem isOpenEmbedding_openCellCoord :
    IsOpenEmbedding (openCellCoord (M := M) (U := U) (V := V)) := by
  let e := (hhomeo.homeomorph (leviUnipotentCoord hP)).prodCongr (Homeomorph.refl V)
  exact hcell.comp e.isOpenEmbedding

/-- Openness of both truncation conditions gives openness of the actual cell. -/
theorem isOpen_conjugationTruncatedCell {A : Set Γ} {B : Set V}
    (hA : IsOpen A) (hB : IsOpen B) (a : M) :
    IsOpen (conjugationTruncatedCell hMU A B a) := by
  apply (isOpenEmbedding_openCellCoord hP hhomeo hcell).isOpenMap
  have hc : Continuous (fun x : (M × U) × V =>
      (a : Γ) * (conjUnipotent hMU x.1.1 x.1.2 : Γ) * (a : Γ)⁻¹) := by
    simp only [conjUnipotent]
    fun_prop
  exact (hA.preimage hc).inter (hB.preimage continuous_snd)

omit [IsTopologicalGroup Γ] in
/-- Uniqueness of the open-cell coordinates recovers the two truncation
conditions, with the precise conjugation orientation. -/
theorem mem_conjugationTruncatedCell_iff (A : Set Γ) (B : Set V)
    (a m : M) (u : U) (v : V) :
    (m : Γ) * u * (v : Γ)⁻¹ ∈ conjugationTruncatedCell hMU A B a ↔
      (a : Γ) * (conjUnipotent hMU m u : Γ) * (a : Γ)⁻¹ ∈ A ∧ v ∈ B := by
  change openCellCoord ((m, u), v) ∈ openCellCoord '' _ ↔ _
  exact (isOpenEmbedding_openCellCoord hP hhomeo hcell).injective.mem_set_image

end Cell

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

local instance rationalSplitSecondCountable : SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G
local instance rationalSplitT2 : T2Space (rationalPoints G) := rationalPoint_t2Space F G
local instance rationalSplitSubgroupSecondCountable (L : Subgroup (rationalPoints G)) :
    SecondCountableTopology L :=
  TopologicalSpace.Subtype.secondCountableTopology (L : Set (rationalPoints G))

open Langlands.BruhatTits.DynamicUnipotentContainment
open Langlands.Aubert.General
open Langlands.Plancherel.RationalDynamicSource

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))
local notation "Pχ" => SubgroupFunctor.carrier (Dynamic.parabolic χ) X₀
local notation "Mχ" => SubgroupFunctor.carrier (Dynamic.centralizer χ) X₀
local notation "Uχ" => unipotentPoints χ
local notation "Vχ" => unipotentPoints (oppositeCocharacter χ)
local notation "hMUχ" => IsSemidirectDecomposition.levi_le_normalizer
  (dynamic_isSemidirectDecomposition χ X₀)
local notation "hPχ" => Langlands.Plancherel.semidirectCoordMem
  (dynamic_isSemidirectDecomposition χ X₀)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The original dynamic centralizer also normalizes the opposite radical. -/
theorem rationalDynamicCentralizer_le_normalizer_opposite :
    Mχ ≤ Subgroup.normalizer (Vχ : Set (rationalPoints G)) := by
  rw [← Dynamic.centralizer_inverseCocharacter χ]
  exact Dynamic.centralizer_le_normalizer_unipotent (oppositeCocharacter χ) X₀

/-- The literal ambient cell for a compact open subgroup and dynamic
parabolic, without a lattice restriction on the conjugator. -/
def rationalDynamicConjugationCell (H : OpenSubgroup (rationalPoints G)) (a : Mχ) :
    Set (rationalPoints G) :=
  conjugationTruncatedCell hMUχ (H : Set (rationalPoints G))
    (H.toSubgroup.subgroupOf Vχ : Set Vχ) a

/-- The actual truncated cell is open, hence measurable. -/
theorem isOpen_rationalDynamicConjugationCell (hG : IsConnectedReductive G)
    (H : OpenSubgroup (rationalPoints G)) (a : Mχ) :
    IsOpen (rationalDynamicConjugationCell χ H a) := by
  have := hG.smooth
  exact isOpen_conjugationTruncatedCell hMUχ hPχ
    (isHomeomorph_leviUnipotentCoord_rationalPoint F G χ)
    (isOpenEmbedding_openCellMap_rationalPoint F G χ)
    H.isOpen (H.isOpen.preimage continuous_subtype_val) a

/-- The exact cell membership condition used in the Haar split. -/
theorem mem_rationalDynamicConjugationCell_iff (hG : IsConnectedReductive G)
    (H : OpenSubgroup (rationalPoints G)) (a m : Mχ) (u : Uχ) (v : Vχ) :
    (m : rationalPoints G) * u * (v : rationalPoints G)⁻¹ ∈
        rationalDynamicConjugationCell χ H a ↔
      (a : rationalPoints G) * (conjUnipotent hMUχ m u : rationalPoints G) *
        (a : rationalPoints G)⁻¹ ∈ H ∧ (v : rationalPoints G) ∈ H := by
  have := hG.smooth
  exact mem_conjugationTruncatedCell_iff hMUχ hPχ
    (isHomeomorph_leviUnipotentCoord_rationalPoint F G χ)
    (isOpenEmbedding_openCellMap_rationalPoint F G χ) _ _ a m u v

variable (H : OpenSubgroup (rationalPoints G))
  (hH : IsCompact (H : Set (rationalPoints G)))
  (muG : Measure (rationalPoints G))

/-- The actual scalar in the open-cell split, with arbitrary ambient Haar
measure and the displayed normalized Levi and radical Haar measures. -/
def rationalDynamicConjugationScalar : ℂ :=
  (((muG H * (openCellConstant
    (leviUnipotentMeasure hPχ (leviHaar χ H hH) (radicalHaar χ H hH))
    (radicalHaar (oppositeCocharacter χ) H hH) H)⁻¹).toReal : ℝ) : ℂ)

/-- The actual VIII.3.1 integral split. The integrand is assumed integrable;
no analytic decay estimate, compact-limit stability, or matrix-height
adaptation is required for this identity. -/
theorem rationalConjugationPairing_eq_dynamic_split
    (hG : IsConnectedReductive G) [muG.IsHaarMeasure]
    {f₁ f₂ : rationalPoints G → ℂ}
    (hf₁ : IsBiInvariant H.toSubgroup f₁) (hf₂ : IsBiInvariant H.toSubgroup f₂)
    (a : Mχ) (hint : Integrable (conjugationIntegrand f₁ f₂ a) muG) :
    conjugationPairing muG f₁ f₂ a =
      ∫ g in (rationalDynamicConjugationCell χ H a)ᶜ,
          conjugationIntegrand f₁ f₂ a g ∂muG +
        rationalDynamicConjugationScalar χ H hH muG *
          ∫ m : Mχ,
            cuspidalFactor (rationalDynamicCentralizer_le_normalizer_opposite χ)
              (radicalHaar (oppositeCocharacter χ) H hH)
              (leviModulus χ)⁻¹ (H.toSubgroup.subgroupOf Vχ : Set Vχ) f₁
              a (a * m * a⁻¹) *
            unipotentFactor (radicalHaar χ H hH) (leviModulus χ)
              {u : Uχ | (a : rationalPoints G) * u * (a : rationalPoints G)⁻¹ ∈ H}
              f₂ m ∂(leviHaar χ H hH) := by
  have := hG.smooth
  let : LocallyCompactSpace Pχ :=
    (isClosed_dynamic_parabolic F G χ).locallyCompactSpace
  let : LocallyCompactSpace Mχ := (isClosed_levi χ).locallyCompactSpace
  let : LocallyCompactSpace Uχ := (isClosed_unipotentPoints χ).locallyCompactSpace
  let : LocallyCompactSpace Vχ :=
    (isClosed_unipotentPoints (oppositeCocharacter χ)).locallyCompactSpace
  have : muG.IsMulRightInvariant := Langlands.Haar.isMulRightInvariant_of_modularCharacter_eq_one
    (rationalPoints_modularCharacter_eq_one hG) muG
  have hMV : Mχ ≤ Subgroup.normalizer (Vχ : Set (rationalPoints G)) := by
    exact rationalDynamicCentralizer_le_normalizer_opposite χ
  exact integral_conj_mul_eq_split hMUχ hPχ muG
    (leviHaar χ H hH) (radicalHaar χ H hH)
    (radicalHaar (oppositeCocharacter χ) H hH)
    (isHomeomorph_leviUnipotentCoord_rationalPoint F G χ)
    (isOpenEmbedding_openCellMap_rationalPoint F G χ)
    (Langlands.Plancherel.rationalDynamicOpenCellConull F G hG χ muG inferInstance)
    H.isOpen.measurableSet (H.isOpen.measure_ne_zero muG ⟨1, H.one_mem⟩) hH.measure_lt_top.ne
    (Langlands.Plancherel.isConjModulus_semidirect_closedCharacter
      (dynamic_isSemidirectDecomposition χ X₀)
      (radicalHaar χ H hH) (isClosed_unipotentPoints χ))
    hMV (fun _ => rfl)
    (fun z hz x => by simpa using hf₁ z hz 1 H.one_mem x)
    (fun z hz x => by simpa using hf₂ 1 H.one_mem z hz x)
    a (isOpen_rationalDynamicConjugationCell χ hG H a).measurableSet
    (mem_rationalDynamicConjugationCell_iff χ hG H a)
    ((H.isOpen.preimage
      ((continuous_const.mul continuous_subtype_val).mul continuous_const)).measurableSet)
    hint

end Rational

end Langlands.HarishChandraSchwartz
