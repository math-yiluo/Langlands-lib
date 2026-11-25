import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConjugationSplit
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConjugationHeightComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviConjugationWeights
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConjugationConvergence
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalFactorDecay
import Langlands.Representation.Aubert.General.RationalOppositeHaarReciprocityProof
import Langlands.Representation.Plancherel.DynamicOppositeHermitianAdjunctionProof

/-! # Estimates for the actual dynamic conjugation split -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.BruhatTits.DynamicUnipotentContainment
open Langlands.Plancherel.RationalDynamicSource

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

local instance : SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G
local instance pointT2 : T2Space (rationalPoints G) := rationalPoint_t2Space F G
private local instance : NonarchimedeanGroup (rationalPoints G) :=
  Langlands.Plancherel.rationalPoints_nonarchimedeanGroup G
local instance subgroupSecondCountable (L : Subgroup (rationalPoints G)) :
    SecondCountableTopology L :=
  TopologicalSpace.Subtype.secondCountableTopology (L : Set (rationalPoints G))

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))
local notation "Mχ" => SubgroupFunctor.carrier (Dynamic.centralizer χ) X₀
local notation "Uχ" => unipotentPoints χ
local notation "Vχ" => unipotentPoints (oppositeCocharacter χ)
local notation "hMU" => IsSemidirectDecomposition.levi_le_normalizer
  (dynamic_isSemidirectDecomposition χ X₀)
local notation "hMV" => rationalDynamicCentralizer_le_normalizer_opposite χ

/-- The actual opposite radical character on the common Levi. -/
abbrev rationalDynamicOppositeModulus : Mχ →* ℝ≥0ˣ :=
  HaarModulus.closedRestrictCharacter Vχ (isClosed_unipotentPoints (oppositeCocharacter χ)) Mχ hMV

/-- The two radical Haar scalings on the common actual Levi are reciprocal. -/
theorem rationalDynamicOppositeModulus_eq_inv (hG : IsConnectedReductive G) :
    rationalDynamicOppositeModulus χ = (leviModulus χ)⁻¹ := by
  apply MonoidHom.ext
  intro m
  have hm : rationalDynamicOppositeModulus χ m * leviModulus χ m = 1 :=
    dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus
      (relativeRootReflectionExistence_of_rootRankOneFactorization rootRankOneFactorization)
      centralSplitTorusCharacter hG χ Vχ Mχ Uχ rfl rfl rfl
      (isClosed_unipotentPoints (oppositeCocharacter χ)) (isClosed_unipotentPoints χ) hMV hMU m
  change rationalDynamicOppositeModulus χ m = (leviModulus χ m)⁻¹
  exact eq_inv_of_mul_eq_one_left hm

variable (H : OpenSubgroup (rationalPoints G))
  (hH : IsCompact (H : Set (rationalPoints G)))

local notation "muM" => leviHaar χ H hH
local notation "muU" => radicalHaar χ H hH
local notation "muV" => radicalHaar (oppositeCocharacter χ) H hH
local notation "δU" => leviModulus χ
local notation "δV" => (leviModulus χ)⁻¹

local instance : LocallyCompactSpace Mχ :=
  (Langlands.Plancherel.RationalDynamicSource.isClosed_levi χ).locallyCompactSpace
local instance : LocallyCompactSpace Uχ := (isClosed_unipotentPoints χ).locallyCompactSpace
local instance : LocallyCompactSpace Vχ :=
  (isClosed_unipotentPoints (oppositeCocharacter χ)).locallyCompactSpace

/-- The actual opposite Haar measure satisfies the inverse modulus rule. -/
theorem isConjModulus_rationalDynamicOpposite (hG : IsConnectedReductive G) :
    IsConjModulus hMV muV δV := by
  rw [← rationalDynamicOppositeModulus_eq_inv χ hG]
  unfold rationalDynamicOppositeModulus
  rw [HaarModulus.closedRestrictCharacter_eq]
  exact isConjModulus_restrictCharacter hMV muV

omit [LocallyOfFiniteType G.X.hom] in
/-- Compactness of the compact intersection used for averaging on the dynamic Levi. -/
theorem compactSpace_subgroupOf_dynamicLevi {K : Subgroup (rationalPoints G)}
    (hK : IsCompact (K : Set (rationalPoints G))) : CompactSpace (K.subgroupOf Mχ) := by
  have hM := Langlands.Plancherel.RationalDynamicSource.isClosed_levi χ
  exact isCompact_iff_compactSpace.mp (hM.isClosedEmbedding_subtypeVal.isCompact_preimage hK)

/-- The height bound on the complement of the actual split cell and the
height cutoff on the opposite tail, for conjugators in the indicated set. -/
def RationalDynamicConjugationHeightBounds (T : Set Mχ) (σ : rationalPoints G → ℝ) : Prop :=
  (∃ C : ℝ, ∀ a ∈ T, ∀ g ∉ rationalDynamicConjugationCell χ H a,
    1 + σ a ≤ C * (1 + σ g + σ ((a : rationalPoints G) * g * (a : rationalPoints G)⁻¹))) ∧
  ∃ b : ℝ, 0 < b ∧ ∀ a ∈ T, ∀ u : Vχ, (a : rationalPoints G)⁻¹ * u * a ∉ H →
    b * (1 + σ a) ≤ 1 + σ u

variable {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

local notation "σ" => rationalHeight (F := F) ρ
local notation "τ" => rationalCompactHeight ρ K.toSubgroup
local notation "Ξ" => rationalXi hKc hPK

/-- The actual split integral has rapid decay on the given set of conjugators
from the corresponding geometric bounds and the stated local analytic estimates. -/
theorem rationalDynamicConjugationIntegralBound
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (muG : Measure (rationalPoints G)) [muG.IsHaarMeasure]
    {T : Set Mχ} {e : rationalPoints G → ℝ} {ΞM eM : Mχ → ℝ}
    (hgeom : RationalDynamicConjugationHeightBounds χ H T σ)
    (hsq : SquareIntegrableWeight muG Ξ σ)
    (hup : XiUpperBound Ξ σ (Subtype.val '' T) e)
    (hwM : haveI := compactSpace_subgroupOf_dynamicLevi χ hKc
      ConvolutionWeights muM (K.toSubgroup.subgroupOf Mχ) ΞM (fun m => τ m))
    (hupM : XiUpperBound ΞM (fun m => σ m) T eM)
    (heM : ∀ a ∈ T, ((δU a : ℝ≥0) : ℝ) * eM a ^ 2 ≤ e a ^ 2)
    (hprod : SigmaProductBound Mχ Vχ σ)
    (h45U : ConstantTermEstimate muU δU Ξ σ ΞM (fun m => σ m))
    (h45V : ConstantTermEstimate muV δV Ξ σ ΞM (fun m => σ m))
    (f₁ f₂ : RationalSchwartzSpace hKc hPK ρ)
    (hf₁ : IsBiInvariant H.toSubgroup (f₁ : rationalPoints G → ℂ))
    (hf₂ : IsBiInvariant H.toSubgroup (f₂ : rationalPoints G → ℂ))
    (hcusp : IsIntegrableUnipotentCuspidal muV (f₁ : rationalPoints G → ℂ)) :
    ConjugationIntegralBound muG T (f₁ : rationalPoints G → ℂ) (f₂ : rationalPoints G → ℂ)
      (fun a => e a) σ := by
  let : CompactSpace K.toSubgroup := isCompact_iff_compactSpace.mp hKc
  let : CompactSpace (K.toSubgroup.subgroupOf Mχ) := compactSpace_subgroupOf_dynamicLevi χ hKc
  let : muG.IsMulRightInvariant := Langlands.Haar.isMulRightInvariant_of_modularCharacter_eq_one
    (rationalPoints_modularCharacter_eq_one hG) muG
  let : Measure.IsMulRightInvariant muM :=
    Langlands.Haar.isMulRightInvariant_of_modularCharacter_eq_one
      (Langlands.Plancherel.DynamicOppositeHermitianAdjunctionProof.levi_modularCharacter_eq_one
        χ hG) muM
  let : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  obtain ⟨_, _, hsemi₁⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (Space.coe_mem f₁)
  obtain ⟨_, _, hsemi₂⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (Space.coe_mem f₂)
  have hwG := rationalConvolutionWeights_of_heightMajorant K.isOpen hKc hPK ρ hG hi hν
    (rationalCompactHeight_isConvolutionHeightMajorant K.isOpen hKc ρ) hsq
  let region (a : rationalPoints G) : Set (rationalPoints G) :=
    {g | ∃ m ∈ T, (m : rationalPoints G) = a ∧ g ∉ rationalDynamicConjugationCell χ H m}
  have hregion (a : Mχ) (ha : a ∈ T) :
      region a = (rationalDynamicConjugationCell χ H a)ᶜ := by
    ext g
    constructor
    · rintro ⟨m, _, hm, hg⟩
      rwa [Subtype.ext hm] at hg
    · intro hg
      exact ⟨a, ha, rfl, hg⟩
  have hheight : ConjugationSigmaBound σ (Subtype.val '' T) region := by
    obtain ⟨C, hC⟩ := hgeom.1
    refine ⟨C, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ g hg
    rw [hregion a ha] at hg
    exact hC a ha g hg
  have hthree := rationalConjugationComplementIntegralBound_of_compactHeight hKc ρ hwG hup
    hheight hsemi₁ hsemi₂
  have hΞ := rationalXi_pos K.isOpen hKc hPK
  have hσ := rationalHeight_nonneg ρ
  have h45U' := h45U.rationalCompactHeight_output hKc ρ (fun m => (hwM.pos m).le)
  have h45V' := h45V.rationalCompactHeight_output hKc ρ (fun m => (hwM.pos m).le)
  have hnuU : IsConjModulus hMU muU δU :=
    Langlands.Plancherel.isConjModulus_semidirect_closedCharacter
      (dynamic_isSemidirectDecomposition χ X₀) muU (isClosed_unipotentPoints χ)
  let trunc (a : Mχ) : Set Uχ :=
    {u | (a : rationalPoints G) * u * (a : rationalPoints G)⁻¹ ∈ H}
  let GammaBar : Set Vχ := H.toSubgroup.subgroupOf Vχ
  have hGammaBar : MeasurableSet GammaBar :=
    (H.isOpen.preimage continuous_subtype_val).measurableSet
  obtain ⟨b, hb, hcut⟩ := hgeom.2
  let t (a : Mχ) : ℝ := b * (1 + σ a)
  have htp (a : Mχ) : 0 < t a := mul_pos hb (by linarith [hσ a])
  have htail (a : Mχ) (ha : a ∈ T) (u : Vχ)
      (hu : u ∈ (conjUnipotent hMV a⁻¹ ⁻¹' GammaBar)ᶜ) :
      t a ≤ 1 + σ u :=
    hcut a ha u (by
      change (a : rationalPoints G)⁻¹ * (u : rationalPoints G) * a ∉ H.toSubgroup
      simpa only [Set.mem_compl_iff, Set.mem_preimage, GammaBar, SetLike.mem_coe,
        Subgroup.mem_subgroupOf, conjUnipotent, Subgroup.coe_inv, inv_inv] using hu)
  have hfactor₁ := cuspidalFactorTailBound_of_constantTermEstimate
    (isConjModulus_rationalDynamicOpposite χ H hH hG) h45V' hΞ hσ hprod hGammaBar hsemi₁
    (fun m => by simpa only [mul_one] using (hcusp m 1).1)
    (fun m => by simpa only [mul_one] using (hcusp m 1).2)
    (fun a _ => htp a) htail (fun _ _ => Set.Subset.rfl)
  have hfactor₂ := unipotentFactorDecayBound_of_constantTermEstimate hnuU h45U' hΞ hσ trunc hsemi₂
  have hτr (k : Mχ) (hk : k ∈ K.toSubgroup.subgroupOf Mχ) (m : Mχ) : τ (m * k) = τ m := by
    simpa only [Subgroup.coe_one, one_mul] using
      rationalCompactHeight_mul_mul ρ K.toSubgroup 1 ⟨k, hk⟩ m
  have hfactor := cuspidalFactorIntegralDecayBound_of_tail hwM hτr hfactor₁ hfactor₂ hσ hupM
    (e₀ := fun a => e a)
    (by simpa only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_inv] using heM)
    ⟨b, hb, fun _ _ => le_rfl⟩
  refine conjugationIntegralBound_of_split
    (S := fun a => (rationalDynamicConjugationCell χ H a)ᶜ)
    (φ₁ := fun a m => cuspidalFactor hMV muV δV GammaBar f₁ a (a * m * a⁻¹))
    (φ₂ := fun a m => unipotentFactor muU δU (trunc a) f₂ m)
    («γ» := rationalDynamicConjugationScalar χ H hH muG) ?_ ?_ hfactor
  · intro a _
    exact rationalConjugationPairing_eq_dynamic_split χ H hH muG hG hf₁ hf₂ a
      (integrable_rationalConjugationIntegrand hKc hPK ρ hsq f₁ f₂ a)
  · intro r
    obtain ⟨c, hc⟩ := hthree r
    refine ⟨c, fun a ha => ?_⟩
    simpa only [hregion a ha] using hc a ⟨a, ha, rfl⟩

end Langlands.HarishChandraSchwartz
