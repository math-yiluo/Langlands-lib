import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalConjugationRankZero
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalDynamicConstantTermTransport
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConjugationGeometry
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviXiReversal
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOppositeCuspidality
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSigmaProduct
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSpecialCompactConstantTermPremises
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalCompactComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalConjugationAdapters

/-! # Assembly of the actual intrinsic cuspidal conjugation bound -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.Aubert.General.RepresentedParabolic (subgroupCongrContinuous)
open Langlands.BruhatTits.SpecialCompact Langlands.BruhatTits.DynamicUnipotentContainment
open Langlands.Plancherel.RationalDynamicSource

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

local notation "Γ" => rationalPoints G
local notation "P₀" => standardParabolicPoints i ν ∅
local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))

variable {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

local notation "σ" => rationalHeight (F := F) ρ
local notation "Ξ" => rationalXi hKc hPK
local notation "e₀" => iwasawaWeight hPK (rationalMinimalModulus i ν)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
private theorem rootSet_erase_simpleRoot [Fintype (SimpleRoot i ν)] [DecidableEq (SimpleRoot i ν)]
    (α : SimpleRoot i ν) :
    rootSet i ν (Finset.univ.erase α) = simpleRelativeRoots i ν \ {α.val} := by
  ext b
  constructor
  · intro hb
    obtain ⟨β, hβ, rfl⟩ := (mem_rootSet i ν _ _).mp hb
    exact ⟨β.2, fun he => (Finset.mem_erase.mp hβ).1 (Subtype.ext he)⟩
  · rintro ⟨hb, hba⟩
    refine (mem_rootSet i ν _ _).mpr ⟨⟨b, hb⟩, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, rfl⟩
    exact fun e => hba (congrArg Subtype.val e)

private theorem rationalCuspidalConjugationSectorBound
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (α : characterLattice S) (hα : α ∈ simpleRelativeRoots i ν)
    {K0 : Subgroup Γ} (hK0o : IsOpen (K0 : Set Γ)) (hK0c : IsCompact (K0 : Set Γ))
    (hbasis : SimultaneousStandardBasisAt i ν K0) (hcover : FiniteCartanCovering F i ν K0)
    (hLcover : StandardLeviCartanCovering F i ν (simpleRelativeRoots i ν \ {α}) K0)
    (hM : IsIwasawaPair (Subgroup.subgroupOf P₀ (standardLeviPoints i ν (simpleRelativeRoots i ν \ {α})))
      (K.toSubgroup.subgroupOf (standardLeviPoints i ν (simpleRelativeRoots i ν \ {α}))))
    (hρ : IsClosedSubgroup ρ)
    (hupper : RationalXiUpperBoundStatement.{u}) (h45 : RationalConstantTermEstimateStatement.{u})
    (muG : Measure Γ) [muG.IsHaarMeasure]
    (hsq : SquareIntegrableWeight muG Ξ σ)
    (hup : XiUpperBound Ξ σ (rationalMinimalChamber i ν) e₀)
    (H : OpenSubgroup Γ) (hH : IsCompact (H : Set Γ))
    (f₁ f₂ : RationalSchwartzSpace hKc hPK ρ)
    (hf₁ : IsBiInvariant H.toSubgroup (f₁ : Γ → ℂ))
    (hf₂ : IsBiInvariant H.toSubgroup (f₂ : Γ → ℂ))
    (hcusp : f₁ ∈ rationalCuspidalSubmodule hKc hPK ρ) :
    ConjugationIntegralBound muG (Subtype.val ⁻¹' rationalMinimalRootSector i ν α)
      (f₁ : Γ → ℂ) (f₂ : Γ → ℂ) (rationalConjugationHalfWeight hPK) σ := by
  classical
  let J := simpleRelativeRoots i ν \ {α}
  have hJ : J ⊆ simpleRelativeRoots i ν := Set.sdiff_subset
  have hproper : J ≠ simpleRelativeRoots i ν := by
    intro he
    have ha : α ∈ J := he.symm ▸ hα
    exact ha.2 rfl
  have hmono := hi.isSplitSubtorus.mono
  obtain ⟨⟨ζ, hζ⟩, hstandard⟩ := standardCocharacter F G hG S i hi ν hν J hJ
  let χ := CommGroupScheme.groupHom ζ ≫ i
  let L := (Dynamic.centralizer χ).carrier X₀
  let M := standardLeviPoints i ν J
  have hL : L = M :=
    congrArg (fun Q : SubgroupFunctor G => Q.carrier X₀) (hstandard ζ hζ).2.1.symm
  have hU : unipotentPoints χ = standardUnipotentPoints i ν J :=
    congrArg (fun Q : SubgroupFunctor G => Q.carrier X₀) (hstandard ζ hζ).2.2.symm
  have hrev := standardSubgroups_reversedChamber i ν standardCocharacter hG hi hν
    (relativeRootNegation F G hG S i hi) hζ
  have hV : unipotentPoints (oppositeCocharacter χ) =
      standardUnipotentPoints i (-ν) (Neg.neg '' J) :=
    congrArg (fun Q : SubgroupFunctor G => Q.carrier X₀) hrev.2.2.symm
  let eL := subgroupCongrContinuous hL
  let TL : Set L := Subtype.val ⁻¹' rationalMinimalRootSector i ν α
  have hDom (a : L) (ha : a ∈ TL) : (a : Γ) ∈ rationalMinimalChamber i ν :=
    (rationalMinimalRootSector_subset α ha).1
  have hgeometry : RationalDynamicConjugationHeightBounds χ H TL σ := by
    obtain ⟨⟨B, _, hB⟩, hb⟩ := rationalConjugationGeometricBounds F G hG S i hi ν hν α hα
      ζ hζ N ρ hρ K hKc hPK H hH
    exact ⟨⟨B, hB⟩, hb⟩
  have hXi : XiUpperBound Ξ σ (Subtype.val '' TL) e₀ := by
    obtain ⟨C, d, he⟩ := hup
    refine ⟨C, d, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact he a (hDom a ha)
  let eM := rationalLeviConjugationHalfWeight hM
  have hLeviXi :
      XiUpperBound (rationalLeviXi hKc hM ∘ eL) (fun m : L => σ m) TL (eM ∘ eL) := by
    obtain ⟨C, d, hb⟩ :=
      rationalLeviXiUpperBound_on_ambientChamber K.isOpen hKc ρ hG hi hν hJ hM hupper hρ hbasis
    exact ⟨C, d, fun a ha => hb (eL a) (hDom a ha)⟩
  have hhalf (a : L) (ha : a ∈ TL) :
      ((leviModulus χ a : ℝ≥0) : ℝ) * (eM ∘ eL) a ^ 2 ≤ e₀ a ^ 2 := by
    let p : Subgroup.subgroupOf P₀ M :=
      ⟨eL a, rationalMinimalChamber_subset_minimalParabolic i ν (hDom a ha)⟩
    have hp := rationalLeviConjugationHalfWeight_sq_mul_modulus K.isOpen hKc hG hi hν hJ hM p
    have he := rationalConjugationHalfWeight_sq hKc hPK
      ⟨a, rationalMinimalChamber_subset_minimalParabolic i ν (hDom a ha)⟩
    change e₀ a ^ 2 = _ at he
    rw [leviModulus_eq_standardUnipotentModulus χ hL hU a, he, mul_comm]
    exact hp.le
  have hJneg : Neg.neg '' J ⊆ simpleRelativeRoots i (-ν) := by
    rw [simpleRelativeRoots_reversed hG hi]
    exact Set.image_mono hJ
  have hprod : SigmaProductBound L (unipotentPoints (oppositeCocharacter χ)) σ := by
    have hRevM : L = standardLeviPoints i (-ν) (Neg.neg '' J) :=
      hL.trans (standardLeviPoints_reversed hG hi hν hJ).symm
    rw [hV, hRevM]
    exact rationalSigmaProductBound hG hi (hν.neg i ν) hJneg ρ hρ
  let hPKneg := hPK.rationalChangeMinimal hG hi hν (hν.neg i ν)
  let hMneg := hM.reversedLevi hG hi hν hJ
  have hCT := rationalDynamicConstantTermEstimates_of_standard hKc hPK ρ χ H hH hG hi hν hJ
    hL hU hV hK0o hK0c hbasis hcover hLcover hPKneg hM hMneg
    (rationalXi_changeMinimal hG hi hν (hν.neg i ν) K.isOpen hKc hPK hPKneg)
    (rationalLeviXi_reversed hG hi hν hJ K.isOpen hKc hM hMneg) hρ h45
  let muL : Measure L := leviHaar χ H hH
  let muM : Measure M := muL.map eL
  let : LocallyCompactSpace L := (Langlands.Plancherel.RationalDynamicSource.isClosed_levi χ).locallyCompactSpace
  let : LocallyCompactSpace M := (isClosed_standardLeviPoints i ν J).locallyCompactSpace
  let : muM.IsHaarMeasure := eL.isHaarMeasure_map muL
  let := compactSpace_subgroupOf_dynamicLevi χ hKc
  let := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := J) hKc
  have hwM := rationalLeviConvolutionWeights_of_upperBound K.isOpen hKc ρ hG hi hν hJ hM hupper
    hρ hK0o hK0c hbasis hLcover muM
  have hwL := hwM.of_subgroupCongr hL
  have hfinite := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  let : Fintype (SimpleRoot i ν) := hfinite.fintype
  let I : Finset (SimpleRoot i ν) := Finset.univ.erase ⟨α, hα⟩
  have hI : rootSet i ν I = J := rootSet_erase_simpleRoot ⟨α, hα⟩
  let muV : Measure (oppositeUnipotent i ζ) := radicalHaar (oppositeCocharacter χ) H hH
  let : LocallyCompactSpace (oppositeUnipotent i ζ) :=
    (isClosed_unipotentPoints (oppositeCocharacter χ)).locallyCompactSpace
  let : muV.IsHaarMeasure :=
    inferInstanceAs (radicalHaar (oppositeCocharacter χ) H hH).IsHaarMeasure
  have hvan := isIntegrableUnipotentCuspidal_opposite_of_mem_rationalCuspidalSubmodule
    hKc hPK ρ hG hi hν I (hI.symm ▸ hproper) ζ (hI.symm ▸ hζ) hcusp muV
  have hbound := rationalDynamicConjugationIntegralBound χ H hH hKc hPK ρ hG hi hν muG
    hgeometry hsq hXi hwL hLeviXi hhalf hprod hCT.1 hCT.2 f₁ f₂ hf₁ hf₂ hvan
  intro r
  obtain ⟨c, hc⟩ := hbound r
  refine ⟨c, fun p hp => ?_⟩
  have hpa : (p : Γ) ∈ rationalMinimalChamber i ν := (rationalMinimalRootSector_subset α hp).1
  have hpL : (p : Γ) ∈ L := by
    rw [hL]
    obtain ⟨t, htp, _⟩ := (mem_rationalMinimalChamber_iff_order i ν (p : Γ)).mp hpa
    rw [← htp]
    exact SubgroupFunctor.le_def.mp (torusCentralizer_le_standardLevi i ν J) _
      (SubgroupFunctor.le_def.mp (range_le_torusCentralizer i) _
        (SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩))
  exact hc ⟨p, hpL⟩ hp

private theorem rationalCuspidalConjugationBound_at_compatible_compact
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hne : (simpleRelativeRoots i ν).Nonempty)
    {K0 : Subgroup Γ} (hK0o : IsOpen (K0 : Set Γ)) (hK0c : IsCompact (K0 : Set Γ))
    (hbasis : SimultaneousStandardBasisAt i ν K0) (hcover : FiniteCartanCovering F i ν K0)
    (hLevi : ∀ J : Set (characterLattice S), J ⊆ simpleRelativeRoots i ν →
      StandardLeviCartanCovering F i ν J K0 ∧
        IsIwasawaPair (Subgroup.subgroupOf P₀ (standardLeviPoints i ν J))
          (K.toSubgroup.subgroupOf (standardLeviPoints i ν J)))
    (hρ : IsClosedSubgroup ρ)
    (hupper : RationalXiUpperBoundStatement.{u}) (h45 : RationalConstantTermEstimateStatement.{u})
    (muG : Measure Γ) [muG.IsHaarMeasure] :
    RationalCuspidalConjugationBound hKc hPK ρ muG := by
  classical
  have hsq := rationalXiSquareIntegrable_of_upperBound hupper F G hG S i hi ν hν K0 hK0o hK0c
    hbasis hcover K.toSubgroup K.isOpen hKc hPK N ρ hρ muG
  have hup := hupper.fullChamberXiUpperBound hG hi hν hbasis K.isOpen hKc hPK hρ
  obtain ⟨R, hR, hsectors⟩ := exists_rationalMinimalRootSector_cover hG hi hne
  apply (rationalCuspidalConjugationBound_iff_generic hKc hPK ρ muG).mpr
  refine ⟨rationalCuspidalConjugationConverges_of_squareIntegrableWeight hKc hPK ρ hsq,
    fun f₁ hcusp f₂ r => ?_⟩
  let : Nonempty (CompactOpenSubgroup Γ) := ⟨⟨K, hKc⟩⟩
  obtain ⟨H₁, h₁, _⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (Space.coe_mem f₁)
  obtain ⟨H₂, h₂, _⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (Space.coe_mem f₂)
  let H : OpenSubgroup Γ := H₁.1 ⊓ H₂.1
  have hH : IsCompact (H : Set Γ) := H₁.2.inter_right H₂.1.isClosed
  have hf₁ : IsBiInvariant H.toSubgroup (f₁ : Γ → ℂ) := h₁.mono inf_le_left
  have hf₂ : IsBiInvariant H.toSubgroup (f₂ : Γ → ℂ) := h₂.mono inf_le_right
  have hB (a : {α // α ∈ R}) := by
    have ha : a.val ∈ simpleRelativeRoots i ν := hR ▸ a.property
    obtain ⟨hLa, hMa⟩ := hLevi (simpleRelativeRoots i ν \ {a.val}) Set.sdiff_subset
    exact rationalCuspidalConjugationSectorBound hKc hPK ρ hG hi hν a.val ha
      hK0o hK0c hbasis hcover hLa hMa hρ hupper h45 muG hsq hup H hH f₁ f₂ hf₁ hf₂ hcusp r
  choose c hc using hB
  refine ⟨∑ a : {α // α ∈ R}, c a, fun p hp => ?_⟩
  have hg : (p : Γ) ∈ rationalMinimalChamberInNormKernel i ν := hp
  rw [hsectors] at hg
  simp only [Set.mem_iUnion] at hg
  obtain ⟨α, hα, hsec⟩ := hg
  let a : {α // α ∈ R} := ⟨α, hα⟩
  have hle : c a ≤ ∑ j : {α // α ∈ R}, c j :=
    Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ a)
  exact (hc a p hsec).trans (mul_le_mul_of_nonneg_right (ENNReal.coe_le_coe.mpr hle) zero_le)

/-- The three remaining global inputs to the actual VIII.3.1 proof assembly. -/
def RationalCuspidalConjugationPrerequisites : Prop :=
  JointSpecialCompactBasisExistenceStatement.{u} ∧
    RationalXiUpperBoundStatement.{u} ∧ RationalConstantTermEstimateStatement.{u}

/-- The exact intrinsic-kernel bound follows from joint compact existence,
the lattice Xi upper estimate and the standard II.4.5 estimate. -/
theorem rationalCuspidalConjugationBound_of_prerequisites
    (h : RationalCuspidalConjugationPrerequisites.{u}) :
    RationalCuspidalConjugationBoundStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν _ _ K hKc hPK N _ ρ hρ muG hmuG
  let := hmuG
  by_cases h0 : simpleRelativeRoots i ν = ∅
  · exact rationalCuspidalConjugationBound_of_simpleRoots_empty hKc hPK ρ hG hi hν h0 hρ muG
  obtain ⟨K0, hK0o, hK0c, hPK0, hbasis, hcover, hLevi⟩ :=
    exists_constantTermPremises_of_joint h.1 hG hi hν
  let K' : OpenSubgroup (rationalPoints G) := ⟨K0, hK0o⟩
  have hPK' : IsIwasawaPair (standardParabolicPoints i ν ∅) K'.toSubgroup := hPK0
  have hK' : IsCompact (K' : Set (rationalPoints G)) := hK0c
  exact rationalCuspidalConjugationBound_of_compact hK' hPK' hKc hPK ρ muG
    (rationalCuspidalConjugationBound_at_compatible_compact hK' hPK' ρ hG hi hν
      (Set.nonempty_iff_ne_empty.mpr h0) hK0o hK0c hbasis hcover hLevi hρ h.2.1 h.2.2 muG)

end Langlands.HarishChandraSchwartz
