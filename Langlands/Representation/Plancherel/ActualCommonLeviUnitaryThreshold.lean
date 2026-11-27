import Langlands.Representation.Plancherel.ActualCommonLeviUnitaryContinuation
import Langlands.Representation.Plancherel.DynamicOppositeConjugationScalar
import Langlands.Representation.Plancherel.DynamicCommonLeviContinuationAssembly
import Langlands.Representation.Plancherel.DynamicCommonLeviPresentationReduction
import Langlands.Representation.Plancherel.ParabolicCharacterDecayProof
import Langlands.Representation.Plancherel.ActualCommonLeviV3Continuation
import Langlands.Representation.Unitary.SmoothCoefficientBoundednessProof
import Langlands.Representation.Unitary.Restriction
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # Explicit convergence thresholds for unitarizable common-Levi data -/

noncomputable section

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

include hG hψ' hψK in
/-- **Explicit convergence threshold for unitarizable inducing data.** For compatible root
presentations of the source and target parabolics on one Levi model and one split component,
and an admissible unitarizable inducing representation, there is a real threshold `R` such that
every parameter whose presentation character lies in the strict full-root region of threshold
`R` is in `pairFullDomainRegion`: the standard integral has full domain on the source normalized
induction of `A ⊗ z`. -/
theorem exists_threshold_mem_pairFullDomainRegion
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
    [Fintype (relativeWeylGroup r.data.i)]
    (hadm : A.IsAdmissible) (hunit : IsUnitarizable A.representation) :
    haveI : Mono r.data.i.hom.hom.left := r.isCompatible.maximalSplit.isSplitSubtorus.mono
    haveI : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left := by
      let := r.isCompatible.splitComponent.1.isSplitSubtorus.mono
      let := r.isCompatible.levi.isClosedSubgroup.mono
      let := r.isCompatible.parabolic.isClosedSubgroup.mono
      have : Mono (a ≫ l ≫ p).hom.hom.left := by
        change Mono (a.hom.hom.left ≫ l.hom.hom.left ≫ p.hom.hom.left)
        infer_instance
      exact mono_of_mono_fac (congrArg (fun z => z.hom.hom.left) r.isCompatible.factor_comp)
    ∃ R : ℝ, ∀ z : unramifiedCharacters (normCharacters χ),
      characterComparison χ ψ r s z ∈ parabolicPointUnramifiedIntertwiningRegion r
          (weylInducedCharacterForm r.isCompatible.splitComponent.1.isSplitSubtorus.1
            r.isCompatible.maximalSplit.isSplitSubtorus.1 r.data.f r.data.i) n q v R →
        z ∈ pairFullDomainRegion χ K hK ψ hψ ψ' A := by
  let g := presentationPointData F G hG χ ψ ψ hψ hψ T M P P U U
    p l p l a n n r s s K hψK hψK
  have h' : IsSemidirectDecomposition ((SubgroupFunctor.range p').carrier (Over.mk (𝟙 _)))
      (parabolicLeviPointSubgroup p l) ((SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 _))) := by
    rw [parabolicPoints_eq χ ψ' s', leviPoints_eq χ ψ s, radicalPoints_eq χ ψ' s']
    exact commonDecomposition χ ψ' hψ'
  have hU' : IsClosed (((SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 _))) :
      Set (rationalPoints G)) := by
    rw [radicalPoints_eq χ ψ' s']
    exact radical_isClosed ψ'
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
    g.decomposition g.radical_closed h' hU'
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
  obtain ⟨R, hfullC, -⟩ := exists_region_convergence_domination_of_coneDecay
    r r' hLevi hn hn' rfl rfl rfl g.decomposition g.radical_closed h' hU'
    g.parabolic_closed K hK g.factorization g.projection_continuous pairMeasure μU μI hμ hsq ρ hρ C hcone
    π hadm' hgrowth
  refine ⟨R, fun z hz => ?_⟩
  exact mem_pairFullDomainRegion χ ψ ψ' hψ r s s' g.decomposition g.radical_closed K hK A z
    (hfullC ⟨characterComparison χ ψ r s z, hz⟩)

/-- The presentation character comparison of `ParabolicData` is the transport along the
presentation's own Levi point identification. -/
theorem characterComparison_parabolicData {T : CommGroupScheme (Spec (CommRingCat.of F))}
    {a : T.toGrp ⟶ parameterScheme χ} (d : ParabolicData χ ψ T a)
    (z : unramifiedCharacters (normCharacters χ)) :
    characterComparison χ ψ d.r d.realizes z = parabolicLeviUnramifiedCharactersHomeomorph d.r z := by
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro m
  change z.val ((parameterPointComparison χ ψ d.realizes).symm m) =
    z.val ((parabolicLeviPointHomeomorph d.r).symm m)
  congr 1
  apply (parameterPointComparison χ ψ d.realizes).injective
  rw [ContinuousMulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [parameterPointComparison_coe, parameterHomeomorph_apply_coe]
  have h := parabolicLeviPointHomeomorph_apply_coe d.r ((parabolicLeviPointHomeomorph d.r).symm m)
  rw [ContinuousMulEquiv.apply_symm_apply, rationalPoints.map_apply] at h
  rw [h]
  exact congrArg (fun f => ((parabolicLeviPointHomeomorph d.r).symm m) ≫ f.hom.hom) d.levi_comp

include hG hψ' hψK in
/-- **The threshold on the Levi parameters themselves.** For presentations sharing the actual
centralizer scheme of `χ` and one split component, the threshold of
`exists_threshold_mem_pairFullDomainRegion` reads directly on the unramified parameters of the
centralizer scheme. -/
theorem exists_threshold_mem_pairFullDomainRegion_of_data
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
    (d₁ : ParabolicData χ ψ T a) (d₂ : ParabolicData χ ψ' T a)
    (o : OppositeData (CommGroupScheme.groupHom (-d₂.r.splitComponentCocharacter) ≫ a ≫
      d₂.l ≫ d₂.p))
    [Fintype (relativeWeylGroup d₁.r.data.i)]
    (hadm : A.IsAdmissible) (hunit : IsUnitarizable A.representation) :
    haveI : Mono d₁.r.data.i.hom.hom.left := d₁.r.isCompatible.maximalSplit.isSplitSubtorus.mono
    haveI : Mono (CommGroupScheme.groupHom d₁.r.data.f).hom.hom.left := by
      let := d₁.r.isCompatible.splitComponent.1.isSplitSubtorus.mono
      let := d₁.r.isCompatible.levi.isClosedSubgroup.mono
      let := d₁.r.isCompatible.parabolic.isClosedSubgroup.mono
      have : Mono (a ≫ d₁.l ≫ d₁.p).hom.hom.left := by
        change Mono (a.hom.hom.left ≫ d₁.l.hom.hom.left ≫ d₁.p.hom.hom.left)
        infer_instance
      exact mono_of_mono_fac (congrArg (fun z => z.hom.hom.left) d₁.r.isCompatible.factor_comp)
    ∃ R : ℝ, ∀ z : unramifiedCharacters (normCharacters χ),
      z ∈ parabolicUnramifiedIntertwiningRegion d₁.r
          (weylInducedCharacterForm d₁.r.isCompatible.splitComponent.1.isSplitSubtorus.1
            d₁.r.isCompatible.maximalSplit.isSplitSubtorus.1 d₁.r.data.f d₁.r.data.i)
          d₁.n o.q o.v R →
        z ∈ pairFullDomainRegion χ K hK ψ hψ ψ' A := by
  let : LocallyOfFiniteType (parameterScheme χ).X.hom := parameterScheme_locallyOfFiniteType χ
  obtain ⟨R, hR⟩ := exists_threshold_mem_pairFullDomainRegion χ hG K hK ψ hψ hψK ψ' hψ' A
    d₁.r d₂.r (d₁.levi_comp.trans d₂.levi_comp.symm) d₁.radical d₂.radical o.represented o.radical
    d₁.realizes d₂.realizes hadm hunit
  refine ⟨R, fun z hz => hR z ?_⟩
  let : Mono d₁.r.data.i.hom.hom.left := d₁.r.isCompatible.maximalSplit.isSplitSubtorus.mono
  let : Mono (CommGroupScheme.groupHom d₁.r.data.f).hom.hom.left := by
    let := d₁.r.isCompatible.splitComponent.1.isSplitSubtorus.mono
    let := d₁.r.isCompatible.levi.isClosedSubgroup.mono
    let := d₁.r.isCompatible.parabolic.isClosedSubgroup.mono
    have : Mono (a ≫ d₁.l ≫ d₁.p).hom.hom.left := by
      change Mono (a.hom.hom.left ≫ d₁.l.hom.hom.left ≫ d₁.p.hom.hom.left)
      infer_instance
    exact mono_of_mono_fac (congrArg (fun z => z.hom.hom.left) d₁.r.isCompatible.factor_comp)
  change (parabolicLeviUnramifiedCharactersHomeomorph d₁.r).symm
    (characterComparison χ ψ d₁.r d₁.realizes z) ∈ parabolicUnramifiedIntertwiningRegion d₁.r
      (weylInducedCharacterForm d₁.r.isCompatible.splitComponent.1.isSplitSubtorus.1
        d₁.r.isCompatible.maximalSplit.isSplitSubtorus.1 d₁.r.data.f d₁.r.data.i) d₁.n o.q o.v R
  rw [characterComparison_parabolicData, ContinuousMulEquiv.symm_apply_apply]
  exact hz

end Langlands.Plancherel.ActualCommonLeviV3
