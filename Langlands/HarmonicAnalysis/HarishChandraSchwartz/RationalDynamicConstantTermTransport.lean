import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalDynamicConjugationEstimate
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalStructuralChamberReversal
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints

/-! # Constant-term estimates on the actual subgroups of the dynamic split -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.Aubert.General.RepresentedParabolic (subgroupCongrContinuous)
open Langlands.BruhatTits.DynamicUnipotentContainment
open Langlands.Plancherel.RationalDynamicSource

namespace Langlands.HarishChandraSchwartz

section Transport

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  {M M' U U' : Subgroup Γ}

omit [MeasurableSpace Γ] [BorelSpace Γ] in
@[simp] private theorem coe_subgroupCongrContinuous (hM : M = M') (m : M) :
    (subgroupCongrContinuous hM m : Γ) = m := rfl

/-- Transport a normalized constant-term estimate along two equalities of
actual subgroups, preserving the scale of the measure. -/
theorem ConstantTermEstimate.of_subgroupCongr
    (hM : M = M') (hU : U = U') {muU : Measure U}
    {δ : M →* ℝ≥0ˣ} {δ' : M' →* ℝ≥0ˣ}
    {Ξ Ξ' σ : Γ → ℝ} {ΞM σM : M → ℝ} {ΞM' σM' : M' → ℝ}
    (hδ : ∀ m, δ' (subgroupCongrContinuous hM m) = δ m)
    (hΞ : ∀ g, Ξ' g = Ξ g)
    (hΞM : ∀ m, ΞM' (subgroupCongrContinuous hM m) = ΞM m)
    (hσM : ∀ m, σM' (subgroupCongrContinuous hM m) = σM m)
    (h : ConstantTermEstimate (muU.map (subgroupCongrContinuous hU)) δ' Ξ' σ ΞM' σM') :
    ConstantTermEstimate muU δ Ξ σ ΞM σM := by
  intro d
  obtain ⟨d', c, hc⟩ := h d
  refine ⟨d', c, fun m => ?_⟩
  let e := (subgroupCongrContinuous hU).toHomeomorph.toMeasurableEquiv
  have hcoe (u : U) : (e u : Γ) = u := rfl
  have hm := hc (subgroupCongrContinuous hM m)
  change (NNReal.sqrt (δ' (subgroupCongrContinuous hM m)) : ℝ≥0∞) *
      ∫⁻ u : U', ENNReal.ofReal (Ξ' ((subgroupCongrContinuous hM m : Γ) * u) *
          (1 + σ ((subgroupCongrContinuous hM m : Γ) * u)) ^ (-d')) ∂(muU.map e) ≤
      c * ENNReal.ofReal (ΞM' (subgroupCongrContinuous hM m) *
        (1 + σM' (subgroupCongrContinuous hM m)) ^ (-d)) at hm
  rw [lintegral_map_equiv _ e] at hm
  simpa only [hδ, hΞ, hΞM, hσM, coe_subgroupCongrContinuous, hcoe] using hm

variable [IsTopologicalGroup Γ] {K : Subgroup Γ}

/-- Transport convolution weights along an equality of the Levi subgroups,
including the normalized average on the intersection with the ambient compact. -/
theorem ConvolutionWeights.of_subgroupCongr
    (hM : M = M') [CompactSpace (K.subgroupOf M)] [CompactSpace (K.subgroupOf M')]
    {muM : Measure M} {Ξ σ : M' → ℝ}
    (h : ConvolutionWeights (muM.map (subgroupCongrContinuous hM)) (K.subgroupOf M') Ξ σ) :
    ConvolutionWeights muM (K.subgroupOf M) (Ξ ∘ subgroupCongrContinuous hM)
      (σ ∘ subgroupCongrContinuous hM) := by
  subst M'
  change ConvolutionWeights muM (K.subgroupOf M) Ξ σ
  change ConvolutionWeights (muM.map id) (K.subgroupOf M) Ξ σ at h
  rwa [Measure.map_id] at h

end Transport

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {J : Set (characterLattice S)}
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (H : OpenSubgroup (rationalPoints G)) (hH : IsCompact (H : Set (rationalPoints G)))

local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))
local notation "Mχ" => SubgroupFunctor.carrier (Dynamic.centralizer χ) X₀
local notation "Uχ" => unipotentPoints χ
local notation "Vχ" => unipotentPoints (oppositeCocharacter χ)
local notation "M₊" => standardLeviPoints i ν J
local notation "M₋" => standardLeviPoints i (-ν) (Neg.neg '' J)
local notation "U₊" => standardUnipotentPoints i ν J
local notation "U₋" => standardUnipotentPoints i (-ν) (Neg.neg '' J)
local notation "σ" => rationalHeight (F := F) ρ
local notation "Ξ" => rationalXi hKc hPK
local notation "muU" => radicalHaar χ H hH
local notation "muV" => radicalHaar (oppositeCocharacter χ) H hH

/-- The two constant-term estimates with the precise integration measures
and the shared Levi weight in the dynamic conjugation split. -/
def RationalDynamicConstantTermEstimates (ΞM : Mχ → ℝ) : Prop :=
  ConstantTermEstimate muU (leviModulus χ) Ξ σ ΞM (fun m => σ m) ∧
  ConstantTermEstimate muV (leviModulus χ)⁻¹ Ξ σ ΞM (fun m => σ m)

/-- The forward dynamic modulus agrees with the standard modulus under the
point-preserving equalities of the two subgroups. -/
theorem leviModulus_eq_standardUnipotentModulus (hM : Mχ = M₊) (hU : Uχ = U₊) (m : Mχ) :
    leviModulus χ m = standardUnipotentModulus i ν J (subgroupCongrContinuous hM m) :=
  Langlands.Jacquet.closedRestrictCharacter_congr hU (isClosed_unipotentPoints χ)
    (isClosed_standardUnipotentPoints i ν J)
    (dynamic_isSemidirectDecomposition χ X₀).levi_le_normalizer
    (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J) rfl

/-- Apply the standard constant-term estimate to both chamber presentations.
The two Xi comparisons identify their weights at the same ambient points. -/
theorem rationalDynamicConstantTermEstimates_of_standard
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (hM : Mχ = M₊) (hU : Uχ = U₊) (hV : Vχ = U₋)
    {K0 : Subgroup (rationalPoints G)} (hK0o : IsOpen (K0 : Set (rationalPoints G)))
    (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : Langlands.BruhatTits.SpecialCompact.SimultaneousStandardBasisAt i ν K0)
    (hcover : FiniteCartanCovering F i ν K0) (hLcover : StandardLeviCartanCovering F i ν J K0)
    (hPK' : IsIwasawaPair (standardParabolicPoints i (-ν) ∅) K.toSubgroup)
    (hMF : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf M₊) (K.toSubgroup.subgroupOf M₊))
    (hMR : IsIwasawaPair ((standardParabolicPoints i (-ν) ∅).subgroupOf M₋)
      (K.toSubgroup.subgroupOf M₋))
    (hΞ : ∀ g, rationalXi hKc hPK' g = Ξ g)
    (hΞM : ∀ (m : M₊) (m' : M₋), (m : rationalPoints G) = m' →
      rationalLeviXi hKc hMR m' = rationalLeviXi hKc hMF m)
    (hρ : IsClosedSubgroup ρ) (hc : RationalConstantTermEstimateStatement.{u}) :
    RationalDynamicConstantTermEstimates hKc hPK ρ χ H hH
      (rationalLeviXi hKc hMF ∘ subgroupCongrContinuous hM) := by
  let muForward : Measure U₊ := Measure.map (subgroupCongrContinuous hU) muU
  let : LocallyCompactSpace Uχ := (isClosed_unipotentPoints χ).locallyCompactSpace
  let : LocallyCompactSpace Vχ :=
    (isClosed_unipotentPoints (oppositeCocharacter χ)).locallyCompactSpace
  let : LocallyCompactSpace U₊ := (isClosed_standardUnipotentPoints i ν J).locallyCompactSpace
  let : LocallyCompactSpace U₋ :=
    (isClosed_standardUnipotentPoints i (-ν) (Neg.neg '' J)).locallyCompactSpace
  let : muForward.IsHaarMeasure := (subgroupCongrContinuous hU).isHaarMeasure_map muU
  have hForward := hc.constantTermEstimate hG hi hν hJ hK0o hK0c hbasis hcover hLcover
    K.isOpen hKc hPK hMF hρ muForward
  have hRev : Mχ = M₋ := hM.trans (standardLeviPoints_reversed hG hi hν hJ).symm
  let muReverse : Measure U₋ := Measure.map (subgroupCongrContinuous hV) muV
  let : muReverse.IsHaarMeasure := (subgroupCongrContinuous hV).isHaarMeasure_map muV
  have hJ' : Neg.neg '' J ⊆ simpleRelativeRoots i (-ν) := by
    rw [simpleRelativeRoots_reversed hG hi]
    exact Set.image_mono hJ
  have hReverse := hc.constantTermEstimate hG hi (hν.neg i ν) hJ' hK0o hK0c
    (simultaneousStandardBasisAt_reversed hG hi hν hbasis)
    (finiteCartanCovering_reversed hG hi hcover)
    (standardLeviCartanCovering_reversed hG hi hν hJ hLcover)
    K.isOpen hKc hPK' hMR hρ muReverse
  refine ⟨hForward.of_subgroupCongr hM hU (σM' := fun m : M₊ => σ m)
    (fun m => (leviModulus_eq_standardUnipotentModulus χ hM hU m).symm)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl), ?_⟩
  refine hReverse.of_subgroupCongr hRev hV (σM' := fun m : M₋ => σ m) ?_ hΞ
    (fun m => hΞM (subgroupCongrContinuous hM m) (subgroupCongrContinuous hRev m) rfl)
    (fun _ => rfl)
  intro m
  have hm := Langlands.Jacquet.closedRestrictCharacter_congr hV
    (isClosed_unipotentPoints (oppositeCocharacter χ))
    (isClosed_standardUnipotentPoints i (-ν) (Neg.neg '' J))
    (rationalDynamicCentralizer_le_normalizer_opposite χ)
    (standardLeviPoints_le_normalizer_standardUnipotentPoints i (-ν) (Neg.neg '' J))
    (m := m) (m' := subgroupCongrContinuous hRev m) rfl
  change rationalDynamicOppositeModulus χ m =
    standardUnipotentModulus i (-ν) (Neg.neg '' J) (subgroupCongrContinuous hRev m) at hm
  rw [rationalDynamicOppositeModulus_eq_inv χ hG] at hm
  exact hm.symm

end Langlands.HarishChandraSchwartz
