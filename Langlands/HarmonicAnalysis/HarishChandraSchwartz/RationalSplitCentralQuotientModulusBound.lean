import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CompatibleCentralQuotientVolumeBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalChamber
import Langlands.Representation.Aubert.General.RationalRayVolumeIndex
import Langlands.Representation.Jacquet.StandardDynamicConstantTerm

/-! # Inverse-modulus compact-cell bounds for the actual split-central quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact Langlands.QuotientIntegration

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

section Index

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

open Aubert.General Aubert.General.RationalPointFamily in
/-- A simultaneous basis at the separate structural `K0` bounds the ray index
of every compact open subgroup `K`. -/
theorem exists_doubleCosetIndex_uniformizerPowers_le_inverse_modulus
    (hi : IsMaximalSplitTorus i)
    {K0 : Subgroup (rationalPoints G)} (hbasis : SimultaneousStandardBasisAt i ν K0)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G))) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : cocharacterLattice S,
      (∀ β : SimpleRoot i ν, 0 ≤ simpleRootPairing i ν β y) →
      ∀ hyP : uniformizerPowers i (.ofAdd y) ∈ standardParabolicPoints i ν ∅,
        (doubleCosetIndex K.toSubgroup (uniformizerPowers i (.ofAdd y)) : ℝ) ≤
          C * ((rationalMinimalModulus i ν ⟨_, hyP⟩ : ℝ≥0) : ℝ)⁻¹ := by
  have : @LocallyCompactSpace (RationalPoint F G.X) pointTopology :=
    rationalWeightsLocallyCompact
  have : @NonarchimedeanGroup (RationalPoint F G.X) _ pointTopology :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  have hfinite := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  obtain ⟨B, hB, hBJ⟩ := hbasis
  obtain ⟨-, A, q, hcomp, hmem⟩ := hBJ (rootSet i ν ∅) (rootSet_subset i ν ∅)
  obtain ⟨L, hLB, hLK⟩ := hB.2.mem_iff.mp (K.isOpen.mem_nhds K.one_mem)
  obtain ⟨-, -, hLo, hLc⟩ := hB.1 L hLB
  let Lop : OpenSubgroup (RationalPoint F G.X) := ⟨L, hLo⟩
  have hexists : ∃ ζ, IsStandardCocharacter i ν (rootSet i ν ∅) ζ :=
    ⟨ν, by rw [rootSet_empty]; exact isStandardCocharacter_empty_self i ν⟩
  have hU : IsClosed (unipotent i ν ∅ : Set (RationalPoint F G.X)) :=
    isClosed_standardUnipotentPoints i ν _
  have hrel : L.relIndex K.toSubgroup ≠ 0 :=
    relIndex_ne_zero_of_open_compact L hLo K.toSubgroup hK
  refine ⟨(L.relIndex K.toSubgroup : ℝ), by exact_mod_cast Nat.pos_of_ne_zero hrel,
    fun y hdom hyP => ?_⟩
  set w := uniformizerPowers i (.ofAdd y)
  let z : Subgroup.center (levi i ν ∅) := ⟨⟨w, uniformizerPowers_mem_levi i ν ∅ y⟩,
    Subgroup.mem_center_iff.mpr fun m => Subtype.ext
      (commute_uniformizerPowers i ν hfinite ∅ hexists y (by simp) m m.property)⟩
  have hray := standardBasisMember_rayIndex i ν hi hfinite ∅ hexists hU q hcomp Lop hLc
    (hmem L hLB) y (by simp) (fun β _ => hdom β) z rfl
  have hδ : HaarModulus.closedRestrictCharacter (unipotent i ν ∅) hU (levi i ν ∅)
      (levi_le_normalizer i ν ∅) (z : levi i ν ∅) = rationalMinimalModulus i ν ⟨w, hyP⟩ :=
    Jacquet.closedRestrictCharacter_congr
      (congrArg (standardUnipotentPoints i ν) (rootSet_empty i ν)) hU
      (isClosed_standardUnipotentPoints i ν ∅) (levi_le_normalizer i ν ∅)
      (standardParabolicPoints_le_normalizer_standardUnipotentPoints i ν ∅) rfl
  rw [hδ] at hray
  have hidx := (doubleCosetIndex_le hLK w hray.1 hrel).2
  calc
    (doubleCosetIndex K.toSubgroup w : ℝ) ≤
        (doubleCosetIndex L w : ℝ) * (L.relIndex K.toSubgroup : ℝ) := by
      exact_mod_cast hidx
    _ ≤ ((rationalMinimalModulus i ν ⟨w, hyP⟩ : ℝ≥0) : ℝ)⁻¹ *
        (L.relIndex K.toSubgroup : ℝ) :=
      mul_le_mul_of_nonneg_right hray.2 (by positivity)
    _ = _ := mul_comm _ _

end Index

section Volume

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

variable (i ν) in
open Aubert.General Aubert.General.RationalPointFamily in
/-- A uniform inverse-modulus bound for the supplied measure of compact
split-central quotient cells at dominant uniformizer powers. -/
def RationalSplitCentralCellModulusBound
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (s : T.toGrp ⟶ G)
    [MeasurableSpace (LeftQuotient (rationalPoints.map s).range)]
    (muQ : Measure (LeftQuotient (rationalPoints.map s).range))
    (K : OpenSubgroup (rationalPoints G)) (Y : Set (rationalPoints G)) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ y : cocharacterLattice S,
    (∀ β : SimpleRoot i ν, 0 ≤ simpleRootPairing i ν β y) →
    ∀ hyP : uniformizerPowers i (.ofAdd y) ∈ standardParabolicPoints i ν ∅,
      muQ (leftQuotientMap (rationalPoints.map s).range ''
        ((K : Set (rationalPoints G)) * {uniformizerPowers i (.ofAdd y)} * Y)) ≤
        ENNReal.ofReal (C * ((rationalMinimalModulus i ν ⟨_, hyP⟩ : ℝ≥0) : ℝ)⁻¹)

open Aubert.General Aubert.General.RationalPointFamily in
/-- The actual compatible split-central quotient satisfies the inverse-modulus
compact-cell bound along every dominant uniformizer ray. The structural `K0`
and the supplied compact open `K` remain independent choices. -/
theorem exists_rationalSplitCentralQuotient_measure_compact_cell_le_inverse_modulus
    (hi : IsMaximalSplitTorus i)
    {K0 : Subgroup (rationalPoints G)} (hbasis : SimultaneousStandardBasisAt i ν K0)
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (s : T.toGrp ⟶ G) (hs : IsSplitComponent s)
    [MeasurableSpace (rationalPoints.map s).range]
    [BorelSpace (rationalPoints.map s).range]
    [MeasurableSpace (LeftQuotient (rationalPoints.map s).range)]
    [BorelSpace (LeftQuotient (rationalPoints.map s).range)]
    {muG : Measure (rationalPoints G)} [muG.IsMulLeftInvariant]
    {muA : Measure (rationalPoints.map s).range} [muA.IsHaarMeasure]
    [muA.IsMulRightInvariant]
    {muQ : Measure (LeftQuotient (rationalPoints.map s).range)}
    (hQ : IsCompatible (rationalPoints.map s).range muG muA muQ)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    {Y : Set (rationalPoints G)} (hY : IsCompact Y) :
    RationalSplitCentralCellModulusBound i ν s muQ K Y := by
  obtain ⟨C, hC, hcell⟩ :=
    exists_rationalSplitCentralQuotient_measure_compact_cell_le_index s hs hQ K hK hY
  obtain ⟨D, hD, hidx⟩ :=
    exists_doubleCosetIndex_uniformizerPowers_le_inverse_modulus hi hbasis K hK
  refine ⟨C * D, mul_pos hC hD, fun y hdom hyP => (hcell _).trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  calc
    C * (doubleCosetIndex K.toSubgroup (uniformizerPowers i (.ofAdd y)) : ℝ) ≤
        C * (D * ((rationalMinimalModulus i ν ⟨_, hyP⟩ : ℝ≥0) : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (hidx y hdom hyP) hC.le
    _ = _ := by ring

end Volume

end Langlands.HarishChandraSchwartz
