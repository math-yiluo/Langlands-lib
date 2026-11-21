import Langlands.Representation.Plancherel.DynamicCommonLeviContinuationAssembly
import Langlands.Representation.Plancherel.DynamicCommonLeviPresentationReduction
import Langlands.Representation.Plancherel.ParabolicCharacterDecayProof
import Langlands.Representation.Plancherel.ActualCommonLeviV3Continuation
import Langlands.Representation.Unitary.SmoothCoefficientBoundednessProof
import Langlands.Representation.Unitary.Restriction
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # Actual common-Levi continuation for unitarizable inducing data -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option quotPrecheck false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Topology
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviV3

open Aubert.General Induction DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor UnramifiedOperatorFamily
open CompactInduction

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicCommonLeviContinuation.radicalMeasurable
  DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable
  DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable
  DynamicCommonLeviContinuation.quotientBorel
  ambientMeasurable ambientBorel leviMeasurable leviBorel
  leviLocallyCompact parabolicLocallyCompact

open StandardIntertwining DynamicCommonLeviPresentationComparison DynamicCommonLeviStructuralComparison
open DynamicCommonLeviPresentationReduction DynamicCommonLeviPresentations
open Langlands.GroupScheme.MatrixRepresentation

attribute [local instance]
  equalitySubgroupMeasurable equalitySubgroupBorel equalityIntersectionMeasurable equalityIntersectionBorel
  equalityQuotientMeasurable equalityQuotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)
  (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

private theorem commonLeviContinuationExists_of_unitarizable_presentations
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    {M P P' Q U U' V : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
    {p : P ⟶ G} {l : M ⟶ P} {p' : P' ⟶ G} {l' : M ⟶ P'} {a : T.toGrp ⟶ M}
    {n : U ⟶ P} {n' : U' ⟶ P'} {q : Q ⟶ G} {v : V ⟶ Q}
    (r : ParabolicRootPresentation p l a) (r' : ParabolicRootPresentation p' l' a)
    (hLevi : l ≫ p = l' ≫ p')
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n) (hn' : LeviSubgroup.IsGeometricUnipotentRadical n')
    (hQ : (Dynamic.parabolic
      (CommGroupScheme.groupHom (-r'.splitComponentCocharacter) ≫ a ≫ l' ≫ p')).IsRepresentedBy q)
    (hv : LeviSubgroup.IsGeometricUnipotentRadical v)
    (s : Realizes χ ψ p l n) (s' : Realizes χ ψ' p' l' n')
    (hadm : A.IsAdmissible) (hfin : A.HasFiniteLength) (hunit : IsUnitarizable A.representation) :
    CommonLeviContinuationExists χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A := by
  let g := presentationPointData F G hG χ ψ ψ' hψ hψ' T M P P' U U'
    p l p' l' a n n' r s s' K hψK hψ'K
  let : Fintype (relativeWeylGroup r.data.i) := g.weyl
  have := hG.smooth
  have := hG.isSeparated
  let : Mono r.data.i.hom.hom.left := r.isCompatible.maximalSplit.isSplitSubtorus.mono
  let : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left := by
    let := r.isCompatible.splitComponent.1.isSplitSubtorus.mono
    let := r.isCompatible.levi.isClosedSubgroup.mono
    let := r.isCompatible.parabolic.isClosedSubgroup.mono
    have : Mono (a ≫ l ≫ p).hom.hom.left := by
      change Mono (a.hom.hom.left ≫ l.hom.hom.left ≫ p.hom.hom.left)
      infer_instance
    exact mono_of_mono_fac (congrArg (fun z => z.hom.hom.left) r.isCompatible.factor_comp)
  let B := weylInducedCharacterForm r.isCompatible.splitComponent.1.isSplitSubtorus.1
    r.isCompatible.maximalSplit.isSplitSubtorus.1 r.data.f r.data.i
  let C := parabolicPointUnramifiedIntertwiningRegion r B n q v
  let π := presentationRepresentation χ ψ s A
  have hadm' : π.IsAdmissible := representationOfEq_isAdmissible' (leviPoints_eq χ ψ s) A hadm
  have hfin' : π.HasFiniteLength := representationOfEq_hasFiniteLength' (leviPoints_eq χ ψ s) A hfin
  have hunit' : IsUnitarizable π.representation :=
    hunit.comp (subgroupHomeomorphOfEq (leviPoints_eq χ ψ s)).toMonoidHom
  let : LocallyCompactSpace (parabolicLeviPointSubgroup p l) :=
    (isClosed_parabolicLeviPointSubgroup r).locallyCompactSpace
  have hcof := compactOpenCofinal_of_nonarchimedean (parabolicLeviPointSubgroup p l)
  obtain ⟨N, ρ, hρ, hdecay⟩ := parabolicCharacterDecayInput_of_statements relativeRootSystem
    centralSplitTorusCharacter F G hG T M P P' Q U U' V p l p' l' a n n' q v r r'
    hLevi hn hn' hQ hv g.decomposition g.radical_closed K hK g.factorization
  let : Nonempty (Fin (N + 1)) := ⟨0⟩
  have hcone := parabolicOppositeConeDecay_of_characterDecay r hn rfl rfl
    g.decomposition g.radical_closed K hK ρ hρ C hdecay
  have hsq := parabolicSquaredModulusInput_of_statements relativeRootSystem centralSplitTorusCharacter
    F G hG T M P P' U U' p l p' l' a n n' r r' hLevi hn hn'
    g.decomposition g.radical_closed g.decomposition' g.radical_closed'
  let pairMeasure := presentationQuotientMeasure χ ψ s K ψ' s' hK
  let μU := presentationRadicalHaar χ K ψ' s' hK
  let μI := presentationIntersectionHaar χ ψ s K ψ' s' hK
  have hμ := presentationQuotientMeasure_isCompatible χ ψ s K ψ' s' hK
  have hgrowth : HasCommonCoefficientGrowth π
      (fun m => rationalMatrixNorm F ρ (m : rationalPoints G)) := by
    refine ⟨0, fun x ℓ => ?_⟩
    obtain ⟨c, hc, hb⟩ := hunit'.smoothCoefficient_bounded hcof hadm' ℓ x
    refine ⟨c + 1, add_pos_of_nonneg_of_pos hc zero_lt_one, ?_⟩
    intro m
    simp only [pow_zero, mul_one]
    change ‖smoothDualPairing π.representation ℓ (π.representation m x)‖ ≤ c + 1
    exact (hb m).trans (le_add_of_nonneg_right zero_le_one)
  obtain ⟨R, hfullC, hdom⟩ := exists_region_convergence_domination_of_coneDecay
    r r' hLevi hn hn' rfl rfl rfl g.decomposition g.radical_closed g.decomposition' g.radical_closed'
    g.parabolic_closed K hK g.factorization g.projection_continuous pairMeasure μU μI hμ hsq ρ hρ C hcone
    π hadm' hgrowth
  have hδ := parabolicRadical_isUnimodular F G hG T M P U p l a n r hn g.radical_closed
  have hδ' := parabolicRadical_isUnimodular F G hG T M P' U' p' l' a n' r' hn' g.radical_closed'
  have hne : (C R).Nonempty := parabolicPointUnramifiedIntertwiningRegion_nonempty
    r r' hLevi hn hQ hv B (weylInducedCharacterForm_nondegenerate _ _ _ _) R
  have hopen : IsOpen (C R) := isOpen_parabolicPointUnramifiedIntertwiningRegion r B n q v R
  obtain ⟨_, _, _, hfull, hrat, _⟩ := parabolicLevi_intertwiningConclusion_of_dominated.{u, uV, uV}
    r r' hLevi hn hn' rfl rfl rfl g.decomposition g.radical_closed hδ K g.parabolic_closed hK
    g.factorization g.projection_continuous g.decomposition' g.radical_closed' hδ' g.parabolic_closed'
    g.factorization' g.projection_continuous' pairMeasure μU μI hμ hsq π hadm' hfin' (C R)
    ⟨hne, hopen, hfullC, compactIntegralLocallyDominatedOn_saturation g.decomposition g.radical_closed
      hδ K g.parabolic_closed hK g.factorization (parabolicLeviRationalNormCharacters r)
      (continuous_parabolicLeviRationalNormCharacters r) g.projection_continuous π _ pairMeasure hopen (hdom hδ)⟩
  exact continuationExists_of_source hG χ ψ ψ' hψ hψ' r s s' g.decomposition g.radical_closed
    g.decomposition' g.radical_closed' g.parabolic_closed g.parabolic_closed' K hK g.factorization
    g.factorization' g.projection_continuous g.projection_continuous' hψK hψ'K A hδ hδ' hsq
    (subset_unramifiedTwistOrbitSaturation _ _ _) hopen hne hfull hrat
    (operatorSquare hG χ ψ ψ' hψ hψ' r s s' g.decomposition g.radical_closed g.decomposition'
      g.radical_closed' g.parabolic_closed g.parabolic_closed' K hK g.factorization g.factorization'
      g.projection_continuous g.projection_continuous' hψK hψ'K A hδ hδ' hsq)

/-- An admissible, finite-length unitarizable inducing representation has
an actual common-Levi continuation, with the prescribed compact models and measures. -/
theorem commonLeviContinuationExists_of_unitarizable
    (hadm : A.IsAdmissible) (hfin : A.HasFiniteLength) (hunit : IsUnitarizable A.representation) :
    CommonLeviContinuationExists χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A := by
  let c := commonLeviAssemblyData χ ψ ψ' hG hψ hψ'
  let d := c.1
  let o := c.2
  let : LocallyOfFiniteType (parameterScheme χ).X.hom := parameterScheme_locallyOfFiniteType χ
  exact commonLeviContinuationExists_of_unitarizable_presentations χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A
    d.first.r d.second.r d.levi_comp d.first.radical d.second.radical o.represented o.radical
    d.first.realizes d.second.realizes hadm hfin hunit

/-- Choose a continued pair from the unitarizable common-Levi convergence
and rationality result. -/
def continuedPairOfUnitarizable
    (hadm : A.IsAdmissible) (hfin : A.HasFiniteLength) (hunit : IsUnitarizable A.representation) :
    ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A :=
  Classical.choice (by
    obtain ⟨hmod, Ω, hopen, hne, hΩ, _, ⟨p⟩⟩ := commonLeviContinuationExists_of_unitarizable
      χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A hadm hfin hunit
    exact ⟨⟨hmod, Ω, hopen, hne, hΩ, p⟩⟩)

end Langlands.Plancherel.ActualCommonLeviV3
