import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalLeviConstantTermThreshold
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitUniformAnnihilators
import Langlands.Representation.Jacquet.StandardDynamicConstantTerm
import Langlands.Representation.CuspidalSupport.RationalNormKernelPositiveGenerators

/-! # The uniform constant-term threshold of the actual induced orbit -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.Jacquet
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

include hG hi hν in
private theorem standardConstantTerm_eq_of_compatible_components
    {J : Set (characterLattice S)} {ζ : cocharacterLattice S}
    (hζ : IsStandardCocharacter i ν J ζ)
    {A₁ A₂ : CommGroupScheme (Spec (CommRingCat.of F))}
    {q₁ : A₁.toGrp ⟶ S.toGrp} {q₂ : A₂.toGrp ⟶ S.toGrp}
    (hA₁ : IsCompatibleStandardSplitComponent i ν J A₁ q₁)
    (hA₂ : IsCompatibleStandardSplitComponent i ν J A₂ q₂)
    {f : rationalPoints G → ℂ}
    (hf₁ : HasStandardConstantTerm hA₁ f) (hf₂ : HasStandardConstantTerm hA₂ f) :
    standardConstantTerm hA₁ f = standardConstantTerm hA₂ f := by
  let t := SplitTorusValuation.uniformizerUnit F
  have ht := SplitTorusValuation.tendsto_uniformizerUnit_pow_zero F
  have h₁ := (HasStandardConstantTerm.dynamicConstantTerm_eq_of_isStandardCocharacter
    hG hi hν hζ hA₁ t ht hf₁).2
  have h₂ := (HasStandardConstantTerm.dynamicConstantTerm_eq_of_isStandardCocharacter
    hG hi hν hζ hA₂ t ht hf₂).2
  funext m
  let e := standardLeviDynamicEquiv (CommGroupScheme.groupHom ζ ≫ i)
    (standardLevi_eq_dynamic hG hi hν hζ).1
  obtain ⟨x, hx⟩ := e.surjective m
  rw [← hx]
  exact (congrFun h₁ x).symm.trans (congrFun h₂ x)

variable (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)
  (I' : Finset (RationalPointFamily.SimpleRoot i ν))
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {qA : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν I') A qA)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- Every smooth section of the actual unitary-twist orbit has one common
constant-term threshold on the full minimal-Levi closed chamber. -/
theorem rationalOrbitConstantTermThreshold_of_minimalLevi :
    RationalOrbitConstantTermThresholdStatement hG hi hν I hKc hPK π C hC mu hsq I' hA := by
  classical
  intro ζ hζ K0 Borig _ hK0c hBorig hmemorig hsim _ hcovers Φ
  let J := RationalPointFamily.rootSet i ν I'
  have hJ : J ⊆ simpleRelativeRoots i ν := RationalPointFamily.rootSet_subset i ν I'
  obtain ⟨B, hB, hstd⟩ := hsim
  obtain ⟨_, A₁, q₁, hA₁, hmem₁⟩ := hstd J hJ
  obtain ⟨_, A₀, q₀, hA₀, hmem₀⟩ := hstd ∅ (Set.empty_subset _)
  have hred := hasCompactDominantMinimalLeviReduction_of_cartanCovering hG hi hν hK0c
    (hcovers ∅ (Set.empty_subset _))
  let νM := RationalPointFamily.leviRationalNormCharacters i ν I
  let χ' := unitaryUnramifiedInclusion νM
  let R := unitaryOrbitTwistRepresentative νM π
  let orbit := fun χ => unitaryOrbitRepresentativeDiscreteSeriesOrbit νM π C hC mu hsq (R χ)
  let V := fun χ => standardUnramifiedInducedObject hG hi hν I π.obj (χ' χ)
  let f := rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq Φ
  have ht : ∀ χ, ∃ t : CoefficientTensor (V χ), coefficientTensorMap (V χ) t = f (orbit χ) := by
    intro χ
    have hrep := rationalInducedOrbitCoefficientMap_representative hG hi hν I hKc hPK
      π C hC mu hsq Φ (R χ)
    have hm :
        rationalInducedCoefficientMap hG hi hν I hKc hPK
            (R χ).val.obj (R χ).val.property.2 (Φ.val (R χ)) ∈
          LinearMap.range (normalizedCoefficientMap
            (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
            (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
            (R χ).val.obj) := by
      rw [← range_rationalInducedCoefficientMap hG hi hν I hKc hPK
        (R χ).val.obj (R χ).val.property.2]
      exact LinearMap.mem_range_self _ _
    obtain ⟨t, ht⟩ := hm
    exact ⟨t, ht.trans hrep.symm⟩
  choose T hT using ht
  obtain ⟨H, _, _, hbi⟩ :=
    rationalInducedOrbitCoefficientMap_hasUniformBiInvariance hG hi hν I hKc hPK π C hC mu hsq Φ
  have hbi' (χ) (k l : H) (g : rationalPoints G) :
      coefficientTensorMap (V χ) (T χ) ((k : rationalPoints G) * g * (l : rationalPoints G)) =
        coefficientTensorMap (V χ) (T χ) g := by
    rw [hT χ]
    exact hbi (orbit χ) k l g
  have := compactSpace_leftQuotient_standardParabolicPoints_rootSet hG hi hν I hKc hPK
  let h := isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I)
  let hU := isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)
  have hm := continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) h
  have hV (χ) : (V χ).IsAdmissible := by
    exact normalizedInductionFunctor_obj_isAdmissible h hU hm
      (π.obj.twist (χ' χ).val.toMonoidHom (unramifiedCharacter_isOpen_ker _ (χ' χ)))
      ((SmoothRep.isAdmissible_twist_iff _ _ π.obj).mpr π.property.2)
  have hrank : ∀ L ∈ B, ∃ d : ℕ, ∀ χ, Module.finrank ℂ (fixedVectors (V χ).representation L) ≤ d := by
    intro L hL
    let L' := basisOpenSubgroup hB hL
    have hLc : IsCompact (L' : Set (rationalPoints G)) := (hB.1 L hL).2.2.2
    refine ⟨standardInducedFixedOrder hG hi hν I π.obj L', fun χ => ?_⟩
    let e := normalizedInductionCompactTrivialTwistFixedVectorsEquiv h hU
      (isClosed_standardParabolicPoints_rootSet hG hi hν I) π.obj L' hLc
      (χ' χ).val.toMonoidHom (unramifiedCharacter_isOpen_ker _ (χ' χ))
      (Induction.compactSubgroup_le_unramifiedPullback_ker νM
        (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
        h.projection hm (χ' χ))
    exact e.finrank_eq.le
  obtain ⟨t, htpos, hth⟩ :=
    hasUniformMinimalLeviConstantTermThreshold_of_fixedRanks hG hi hν hA₁ hζ hJ hB hmem₁ hA₀ hmem₀
      hred V hV T H hbi' hrank
  refine ⟨t, htpos, fun ω m hmem => ?_⟩
  obtain ⟨χ, rfl⟩ := unitaryOrbitTwistRepresentative_surjective νM π C hC mu hsq ω
  change f (orbit χ) (m : rationalPoints G) =
    standardHalfModulus i ν J (minimalLeviInclusion hG hi hν J m) *
      standardConstantTerm hA (fun g => f (orbit χ) g) (minimalLeviInclusion hG hi hν J m)
  let fχ := fun g => coefficientTensorMap (V χ) (T χ) g
  have hfχ : fχ ∈ coefficientFunctionSpace (V χ) := by
    rw [coefficientFunctionSpace_eq_map]
    exact ⟨_, ⟨T χ, rfl⟩, rfl⟩
  have hCT₁ := (standardConstantTerm_spec hG hi hν hζ hB hA₁ hmem₁
    (V χ).representation (hV χ) hfχ).1
  have hCT := (standardConstantTerm_spec hG hi hν hζ hBorig hA hmemorig
    (V χ).representation (hV χ) hfχ).1
  have heq := standardConstantTerm_eq_of_compatible_components hG hi hν hζ hA₁ hA hCT₁ hCT
  have hs := hth χ m hmem
  change fχ (m : rationalPoints G) =
    standardHalfModulus i ν J (minimalLeviInclusion hG hi hν J m) *
      standardConstantTerm hA₁ fχ (minimalLeviInclusion hG hi hν J m) at hs
  rw [heq] at hs
  simpa only [fχ, hT χ] using hs

end Langlands.HarishChandraSchwartz
