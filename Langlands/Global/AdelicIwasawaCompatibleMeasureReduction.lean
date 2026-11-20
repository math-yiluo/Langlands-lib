import Langlands.Global.AdelicIwasawaCompatibleMeasureStatement
import Langlands.Global.AdelicIwasawaIntegrationStatement
import Langlands.Global.AdelicParabolicModulusStatement
import Langlands.Global.AdelicLocalModularComparison
import Langlands.Global.LocalModularCharacterAdjointDeterminantProof
import Langlands.Global.RepresentedAdelicSubgroupQuotient
import Langlands.Global.AdelicSubgroupHaarNormalization
import Langlands.GroupScheme.Rational.ParabolicRootRadicals
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.AdjointDeterminantExistenceProof

/-! # Iwasawa-compatible Haar measures on `M(𝔸)` from the Iwasawa integration formula -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj NNReal ENNReal CompactlySupported

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

namespace IwasawaCompatibleMeasure

section Subgroup

variable {F : Type} [Field F] [NumberField F]
  {G U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine U.X.left] [LocallyOfFiniteType U.X.hom] (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]

/-- Mathlib's Haar measure on `U(𝔸)`, transported to the closed subgroup `j(U(𝔸))` of `G(𝔸)`,
is a positive multiple of the normalized Haar measure of that subgroup, when `U(F) \ U(𝔸)` is
compact. -/
theorem exists_integral_adelicRangeMap_eq
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range j))] :
    haveI : IsClosed (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j) :
        Set (AdelicGroupPoints F G)) :=
      AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
    ∃ β : ℝ, 0 < β ∧
      ∀ g : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j) → ℂ,
        ∫ u, g (AdelicSubgroupPoints.adelicRangeMap F j u)
            ∂(Measure.haar : Measure (AdelicGroupPoints F U)) =
          β • ∫ v, g v
            ∂(AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range j)) := by
  have hcl : IsClosed (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j) :
      Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  have : LocallyCompactSpace
      (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :=
    hcl.locallyCompactSpace
  let φ := AdelicSubgroupPoints.adelicRangeMap F j
  have hφc : Continuous φ := AdelicSubgroupPoints.continuous_adelicRangeMap F j
  have hφs : Function.Surjective φ := AdelicSubgroupPoints.adelicRangeMap_surjective F j
  have hemb : IsClosedEmbedding (map F U G j) := isClosedEmbedding_map F U G j
  have hφe : IsClosedEmbedding φ := by
    have h1 : IsEmbedding φ := by
      have h0 : IsEmbedding (fun u => ((φ u :
          AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :
            AdelicGroupPoints F G)) := hemb.isEmbedding
      exact (IsEmbedding.subtypeVal.of_comp_iff).mp h0
    exact ⟨h1, by rw [hφs.range_eq]; exact isClosed_univ⟩
  have : (Measure.map φ (Measure.haar : Measure (AdelicGroupPoints F U))).IsHaarMeasure :=
    Measure.isHaarMeasure_map _ φ hφc hφs hφe.tendsto_cocompact
  set b := Measure.haarScalarFactor (Measure.map φ (Measure.haar : Measure (AdelicGroupPoints F U)))
    (Measure.haar : Measure (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)))
    with hbdef
  have hb : Measure.map φ (Measure.haar : Measure (AdelicGroupPoints F U)) =
      b • (Measure.haar :
        Measure (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j))) :=
    Measure.isMulLeftInvariant_eq_smul _ _
  have hbpos : 0 < b := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  set N := AdelicSubgroupPoints.quotientMassNormalizer F G (SubgroupFunctor.range j) with hNdef
  have hN0 : N ≠ 0 := AdelicSubgroupPoints.quotientMassNormalizer_ne_zero F G _
  have hNt : N ≠ ⊤ := AdelicSubgroupPoints.quotientMassNormalizer_ne_top F G _
  have hNpos : 0 < N.toReal := ENNReal.toReal_pos hN0 hNt
  refine ⟨(b : ℝ) / N.toReal, div_pos (by exact_mod_cast hbpos) hNpos, ?_⟩
  intro g
  rw [← hφe.measurableEmbedding.integral_map, hb, integral_smul_nnreal_measure]
  unfold AdelicSubgroupPoints.normalizedHaarMeasure
  rw [integral_smul_measure, ← hNdef, smul_smul, div_mul_cancel₀ _ hNpos.ne', NNReal.smul_def]

end Subgroup

section Modulus

variable {F : Type} [Field F] [NumberField F]

/-- `m^{-2ρ_P}` is the inverse of the idele norm of `det(Ad | Lie P)`. -/
theorem parameterPower_neg_modulusParameter
    (P : GroupScheme (Spec (CommRingCat.of F))) [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
    (q : AdelicGroupPoints F P) :
    parameterPower F P (-modulusParameter F P) q =
      ((((characterNorm F P (Lie.adjointDeterminantCharacter P).toMul q : ℝ≥0) : ℝ))⁻¹ : ℂ) := by
  have hpos : (0 : ℝ) <
      ((characterNorm F P (Lie.adjointDeterminantCharacter P).toMul q : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  rw [parameterPower, modulusParameter, map_neg, LinearMap.neg_apply,
    complexParameterPairing_tmul, characterLog_apply, one_mul, Complex.exp_neg,
    ← Complex.ofReal_exp, Real.exp_log hpos]

/-- Under `AdelicParabolicModulusStatement`, the adelic modulus `δ_P` of a dynamic parabolic is
the idele norm of `det(Ad | Lie P)`. -/
theorem parabolicModulus_eq_characterNorm (hMod : AdelicParabolicModulusStatement.{0})
    {G P U : GroupScheme (Spec (CommRingCat.of F))} (hG : IsConnectedReductive G)
    {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G} {iP : P ⟶ G} {iU : U ⟶ G}
    (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
    (hU : (Dynamic.unipotent χ).IsRepresentedBy iU) :
    haveI := hG.isAffineHom
    haveI : Smooth G.X.hom := hG.smooth
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := isAffine_parabolic F hP
    haveI := locallyOfFiniteType_parabolic F hP
    ∀ q : AdelicGroupPoints F P,
      (parabolicModulus F hP hU q : ℝ≥0) =
        (characterNorm F P (Lie.adjointDeterminantCharacter P).toMul q : ℝ≥0) := by
  have := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := isAffine_parabolic F hP
  have := locallyOfFiniteType_parabolic F hP
  have := isAffine_unipotent F hU
  have := locallyOfFiniteType_unipotent F hU
  intro q
  have h2 := (hMod F G hG χ P U iP iU hP hU _ (Lie.finiteCoordinates U)).2 q
  have hsm : Smooth P.X.hom := (dynamicSmooth F G χ P iP).1 hP
  have h3 := modularCharacter_eq_characterNorm_of_local F P _
    (PlaceGroupPoints.localModularCharacterAdjointDeterminant F P hsm) q
  have h2' : Measure.modularCharacter q = (parabolicModulus F hP hU q : ℝ≥0) := h2
  have h3' : Measure.modularCharacter q =
      (characterNorm F P (Lie.adjointDeterminantCharacter P).toMul q : ℝ≥0) := h3
  rw [← h2', h3']

end Modulus

/-- **Iwasawa-compatible Haar measures exist**, given the Iwasawa integration formula
`AdelicIwasawaIntegrationStatement` and the identification `AdelicParabolicModulusStatement` of
the adelic modulus. -/
theorem iwasawaCompatibleMeasureExistence_of_integration
    (hInt : AdelicIwasawaIntegrationStatement.{0})
    (hMod : AdelicParabolicModulusStatement.{0}) :
    IwasawaCompatibleMeasureExistenceStatement := by
  intro F _ _ G P M U A _ _ _ _ _ _ _ p _ iU l _ a r hG hU K hK _
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  have : Smooth G.X.hom := hG.smooth
  have : Smooth U.X.hom := hU.1.smooth
  have : LocallyOfFiniteType U.X.hom := inferInstance
  let := r.isCompatible.parabolic.isClosedSubgroup.mono
  let := (r.isCompatible.levi.isClosedSubgroup.comp
    r.isCompatible.parabolic.isClosedSubgroup).mono
  have hmU : Mono (iU ≫ p).hom.hom.left := inferInstance
  set χ := CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p with hχ
  have hP : (Dynamic.parabolic χ).IsRepresentedBy p :=
    ⟨Over.mono_of_mono_left _, r.parabolic_eq_splitComponentCocharacter⟩
  have hM : (Dynamic.centralizer χ).IsRepresentedBy (l ≫ p) :=
    ⟨Over.mono_of_mono_left _, r.levi_eq_splitComponentCocharacter⟩
  have hU' : (Dynamic.unipotent χ).IsRepresentedBy (iU ≫ p) :=
    ⟨Over.mono_of_mono_left _, r.range_comp_radical_eq hU⟩
  obtain ⟨c, hc0, hc⟩ :=
    hInt F G hG χ P M U p (l ≫ p) (iU ≫ p) hP hM hU' K hK.isCompact hK.range_mul
  have : CompactSpace
      (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range (iU ≫ p))) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F (iU ≫ p)
      hU.1.smooth hU.1.connectedSpace hU.1.isUnipotent
  obtain ⟨β, hβ0, hβ⟩ := exists_integral_adelicRangeMap_eq (iU ≫ p)
  have hmod := parabolicModulus_eq_characterNorm hMod hG hP hU'
  have hcTP : ∀ m : AdelicGroupPoints F M,
      map F M P (Dynamic.centralizerToParabolic hP hM) m = map F M P l m := fun m =>
    (isClosedEmbedding_map F P G p).injective (by
      rw [← map_comp_apply_of_hom, ← map_comp_apply_of_hom, Dynamic.centralizerToParabolic_comp])
  refine ⟨ENNReal.ofReal ((c : ℝ) * β) • Measure.haar, ?_, ?_⟩
  · exact Measure.IsHaarMeasure.smul _
      (ENNReal.ofReal_pos.mpr (mul_pos (by exact_mod_cast hc0) hβ0)).ne' ENNReal.ofReal_ne_top
  intro f
  refine (hc f).trans ?_
  have : IsClosed (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ p)) :
      Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iU ≫ p)
  -- the innermost integral over `U(𝔸)`
  have hinner : ∀ (k : K) (m : AdelicGroupPoints F M),
      ∫ v, parameterPower F P (-modulusParameter F P) (map F M P l m) *
          f ((v : AdelicGroupPoints F G) * map F P G p (map F M P l m) *
            (k : AdelicGroupPoints F G))
        ∂(AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range (iU ≫ p))) =
      β⁻¹ • ∫ u, ((parabolicModulus F hP hU'
            (map F M P (Dynamic.centralizerToParabolic hP hM) m) : ℝ≥0) : ℝ)⁻¹ •
          f (map F U G (iU ≫ p) u * map F M G (l ≫ p) m * (k : AdelicGroupPoints F G))
        ∂(Measure.haar : Measure (AdelicGroupPoints F U)) := by
    intro k m
    have h := hβ (fun v => parameterPower F P (-modulusParameter F P) (map F M P l m) *
      f ((v : AdelicGroupPoints F G) * map F P G p (map F M P l m) *
        (k : AdelicGroupPoints F G)))
    have hpt : ∀ u : AdelicGroupPoints F U,
        ((parabolicModulus F hP hU'
            (map F M P (Dynamic.centralizerToParabolic hP hM) m) : ℝ≥0) : ℝ)⁻¹ •
          f (map F U G (iU ≫ p) u * map F M G (l ≫ p) m * (k : AdelicGroupPoints F G)) =
        parameterPower F P (-modulusParameter F P) (map F M P l m) *
          f ((AdelicSubgroupPoints.adelicRangeMap F (iU ≫ p) u : AdelicGroupPoints F G) *
            map F P G p (map F M P l m) * (k : AdelicGroupPoints F G)) := by
      intro u
      rw [parameterPower_neg_modulusParameter, hcTP, hmod, map_comp_apply_of_hom l,
        Complex.real_smul, Complex.ofReal_inv]
      rw [show ((AdelicSubgroupPoints.adelicRangeMap F (iU ≫ p) u :
          AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ p))) :
            AdelicGroupPoints F G) = map F U G (iU ≫ p) u from rfl]
    simp_rw [hpt]
    rw [h, smul_smul, inv_mul_cancel₀ hβ0.ne', one_smul]
  symm
  calc _ = ∫ k : K, ((c : ℝ) * β) • ∫ m, β⁻¹ • ∫ u,
          ((parabolicModulus F hP hU'
            (map F M P (Dynamic.centralizerToParabolic hP hM) m) : ℝ≥0) : ℝ)⁻¹ •
          f (map F U G (iU ≫ p) u * map F M G (l ≫ p) m * (k : AdelicGroupPoints F G))
        ∂(Measure.haar : Measure (AdelicGroupPoints F U))
        ∂(Measure.haar : Measure (AdelicGroupPoints F M))
        ∂(compactHaarProbability F G K hK.isCompact) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        dsimp only
        rw [integral_smul_measure, ENNReal.toReal_ofReal
          (mul_pos (by exact_mod_cast hc0) hβ0).le]
        simp_rw [hinner k]
    _ = _ := by
        simp_rw [integral_smul, smul_smul]
        rw [mul_assoc, mul_inv_cancel₀ hβ0.ne', mul_one]

end IwasawaCompatibleMeasure

/-- The existence of an Iwasawa-compatible Haar measure on `M(𝔸)`
(`IwasawaCompatibleMeasureExistenceStatement`) follows from the Iwasawa integration formula
(`AdelicIwasawaIntegrationStatement`) and the identification of the adelic modulus
(`AdelicParabolicModulusStatement`). -/
def IwasawaCompatibleMeasureIntegrationReductionStatement : Prop :=
  AdelicIwasawaIntegrationStatement.{0} → AdelicParabolicModulusStatement.{0} →
    IwasawaCompatibleMeasureExistenceStatement

theorem iwasawaCompatibleMeasureIntegrationReduction :
    IwasawaCompatibleMeasureIntegrationReductionStatement :=
  fun hInt hMod =>
    IwasawaCompatibleMeasure.iwasawaCompatibleMeasureExistence_of_integration hInt hMod

end Langlands.Global
