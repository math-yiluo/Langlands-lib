import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWeightedSynthesis
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardThetaParts
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalSpace

/-! # Convolution with the actual proper source sum in Waldspurger VIII.2.3 -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.GlobalSynthesis

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

local instance sourceConvolutionCompactOpen : Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

variable (hG : IsConnectedReductive G)
  {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  [∀ t, IsAffine (T t).X.left]
  (a : ∀ t, (T t).toGrp ⟶ (chosenLeviModel t).scheme)
  (ha : ∀ t, IsSplitComponent (a t))
  [∀ t, ((chosenLeviModel t).splitCenter (a t)).Normal]
  [∀ t, (rationalPoints.map (a t)).range.Normal]
  [∀ t, MeasurableSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  [∀ t, BorelSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  (muM : ∀ t, Measure (levi t ⧸ (chosenLeviModel t).splitCenter (a t)))
  [∀ t, (muM t).IsHaarMeasure]
  (d : ∀ t : SemistandardSpectralIndex i, CompactData t)
  (rs : ∀ t : SemistandardSpectralIndex i, CocharacterPresentation hG t)
  (hindex : ∀ t, (RenardCartan.splitValuationImage (a t)).FiniteIndex)
  (Q : ∀ t : RationalSemistandardTheta.{u, uV} a ha muM,
    OrbitPacketData (rs t.1)
      (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2))
  (K0 : OpenSubgroup (rationalPoints G)) (hK0 : IsCompact (K0 : Set (rationalPoints G)))
  {nu : cocharacterLattice S} {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))

/-- Both raw convolutions in the proof of VIII.2.3, with the actual source
packet on each literal proper semistandard index. -/
def ProperPacketConvolutionVanishingStatement (muG : Measure (rationalPoints G)) : Prop :=
  ∀ f : RationalSchwartzSpace hKc hPK rho, f ∈ rationalCuspidalSubmodule hKc hPK rho →
    ∀ (t : RationalSemistandardTheta.{u, uV} a ha muM), t.1.IsProper →
      ∀ v : rationalSemistandardThetaComponentSpace.{u, uV} a ha muM d t,
        convolution muG f (componentPacket hG a ha muM d rs hindex Q t v) = 0 ∧
          convolution muG (componentPacket hG a ha muM d rs hindex Q t v) f = 0

set_option hygiene false in
local notation "compactK" => (isCompact_iff_compactSpace.mp hKc :
  CompactSpace (K : Subgroup (rationalPoints G)))

variable {muG : Measure (rationalPoints G)} [muG.IsHaarMeasure] [SFinite muG]
  (hw : letI := compactK
    ConvolutionWeights muG (K : Subgroup (rationalPoints G))
      (rationalXi hKc hPK) (rationalHeight (F := F) rho))

set_option hygiene false in
local notation "C" => RationalSchwartzSpace hKc hPK rho

set_option hygiene false in
local notation "synth" => schwartzSynthesis hG a ha muM d rs hindex Q K0 hK0 hKc hPK rho

/-- A proper-supported actual synthesis can be removed in either convolution
against an intrinsically cuspidal Schwartz function. Component membership
comes from the actual VI.3.1 continuity premise. -/
def ProperSynthesisConvolutionStatement : Prop :=
  letI := compactK
  ∀ (h : SchwartzMembershipStatement hG a ha muM d rs hindex Q K0 hK0 hKc hPK rho),
    ComponentContinuityStatement hG a ha muM d rs hindex Q K0 hKc hPK rho →
    ∀ (hfin : SemistandardSpectralFiberFinitenessStatement.{u}) (hi : IsMaximalSplitTorus i)
      (hnu : IsGenericCocharacter i nu)
      (hspecial : BruhatTits.SpecialCompact.SpecialCompactProperties F i nu
        (K0 : Subgroup (rationalPoints G)))
      (hd : ∀ t, (d t).compact = K0) (hQ : ∀ t, (Q t).compact = K0),
      ProperPacketConvolutionVanishingStatement hG a ha muM d rs hindex Q hKc hPK rho muG →
      ∀ (v : rationalSemistandardThetaSmoothSections.{u, uV} a ha muM d),
        rationalSemistandardThetaSupport.{u, uV} a ha muM v.val ⊆
          rationalSemistandardThetaProper.{u, uV} a ha muM →
        ∀ f₁ f₂ : C, f₁ ∈ rationalCuspidalSubmodule hKc hPK rho →
          Space.convolution hw f₁ f₂ =
            Space.convolution hw f₁ (f₂ - synth h hfin hi hnu hspecial hd hQ v) ∧
          Space.convolution hw f₂ f₁ =
            Space.convolution hw (f₂ - synth h hfin hi hnu hspecial hd hQ v) f₁

set_option maxHeartbeats 800000 in
theorem properSynthesisConvolution :
    ProperSynthesisConvolutionStatement hG a ha muM d rs hindex Q K0 hK0 hKc hPK rho hw := by
  have : CompactSpace (K : Subgroup (rationalPoints G)) := compactK
  intro h hcont hfin hi hnu hspecial hd hQ hvanish v hv f₁ f₂ hf₁
  classical
  let sectionAt (t : RationalSemistandardTheta.{u, uV} a ha muM) :
      ComponentTopologicalSpace a ha muM d t :=
    rationalSemistandardThetaComponent a ha muM d t v
  let packet (t : RationalSemistandardTheta.{u, uV} a ha muM) : C :=
    (hcont hi hnu hspecial hd hQ t).choose (sectionAt t)
  have hpacket (t : RationalSemistandardTheta.{u, uV} a ha muM) :
      (packet t : rationalPoints G → ℂ) =
        componentPacket hG a ha muM d rs hindex Q t (sectionAt t) := by
    funext g
    exact (hcont hi hnu hspecial hd hQ t).choose_spec (sectionAt t) g
  have hsum : synth h hfin hi hnu hspecial hd hQ v =
      ∑ t ∈ v.property.2.toFinset, (sourceWeight hG rs K0 hK0 t.1 : ℂ) • packet t := by
    apply Space.toFunLinear_injective
    rw [map_sum]
    simp only [Space.toFunLinear_apply, Space.coe_smul, hpacket]
    exact weightedSynthesis_eq_sum hG a ha muM d rs hindex Q K0 hK0 v
  have hzero (t : RationalSemistandardTheta.{u, uV} a ha muM)
      (ht : t ∈ v.property.2.toFinset) :
      Space.convolutionBilin hw f₁ (packet t) = 0 ∧
        (Space.convolutionBilin hw).flip f₁ (packet t) = 0 := by
    have htProper := hv (v.property.2.mem_toFinset.mp ht)
    obtain ⟨hleft, hright⟩ := hvanish f₁ hf₁ t htProper (sectionAt t)
    constructor
    · apply Space.toFunLinear_injective
      simpa only [Space.convolutionBilin_apply, Space.toFunLinear_apply,
        Space.coe_convolution, Space.coe_zero, hpacket] using hleft
    · apply Space.toFunLinear_injective
      simpa only [LinearMap.flip_apply, Space.convolutionBilin_apply, Space.toFunLinear_apply,
        Space.coe_convolution, Space.coe_zero, hpacket] using hright
  have hleft : Space.convolutionBilin hw f₁ (synth h hfin hi hnu hspecial hd hQ v) = 0 := by
    rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun t ht => by rw [map_smul, (hzero t ht).1, smul_zero]
  have hright : (Space.convolutionBilin hw).flip f₁ (synth h hfin hi hnu hspecial hd hQ v) = 0 := by
    rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun t ht => by rw [map_smul, (hzero t ht).2, smul_zero]
  constructor
  · change Space.convolutionBilin hw f₁ f₂ =
      Space.convolutionBilin hw f₁ (f₂ - synth h hfin hi hnu hspecial hd hQ v)
    rw [map_sub, hleft, sub_zero]
  · change (Space.convolutionBilin hw).flip f₁ f₂ =
      (Space.convolutionBilin hw).flip f₁ (f₂ - synth h hfin hi hnu hspecial hd hQ v)
    rw [map_sub, hright, sub_zero]

end Langlands.HarishChandraSchwartz.RationalSemistandard.GlobalSynthesis
