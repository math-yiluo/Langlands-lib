import Langlands.Representation.Plancherel.CompactIntegralOpenDomination
import Langlands.Representation.Plancherel.DynamicCommonLeviPointAssembly
import Langlands.Representation.Plancherel.DynamicCommonLeviPresentationReduction
import Langlands.Representation.Plancherel.DynamicCommonLeviPresentations
import Langlands.Representation.Plancherel.ParabolicPointUniformNumerator

/-! # Rationality of actual dynamic compact operators on open full domains -/

noncomputable section

set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

universe u uV

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicCommonLeviContinuation

open Aubert.General Induction StandardIntertwining UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open DynamicCommonLeviCompact DynamicCommonLeviComposition
open DynamicCommonLeviPresentations DynamicCommonLeviPresentationComparison
open DynamicCommonLeviPresentationReduction DynamicCommonLeviStructuralComparison

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

local instance fullDomain_subgroupMeasurable {H : Type u} [Group H] [TopologicalSpace H]
    (U : Subgroup H) : MeasurableSpace U := borel _
local instance fullDomain_subgroupBorel {H : Type u} [Group H] [TopologicalSpace H]
    (U : Subgroup H) : BorelSpace U := ⟨rfl⟩
local instance fullDomain_quotientMeasurable {H : Type u} [Group H] [TopologicalSpace H]
    (U V : Subgroup H) : MeasurableSpace (QuotientSpace (U := U) V) := borel _
local instance fullDomain_quotientBorel {H : Type u} [Group H] [TopologicalSpace H]
    (U V : Subgroup H) : BorelSpace (QuotientSpace (U := U) V) := ⟨rfl⟩

private theorem isUnimodularModulus_of_eq {H : Type u} [Group H] [TopologicalSpace H]
    [LocallyCompactSpace H] [NonarchimedeanGroup H] [T2Space H]
    {U V : Subgroup H} (h : U = V) (hU : IsClosed (U : Set H)) (hV : IsClosed (V : Set H))
    (hδ : IsUnimodularModulus V hV) : IsUnimodularModulus U hU := by
  subst V
  exact hδ

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (hG : IsConnectedReductive G)
  (χ ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (a : T.toGrp ⟶ parameterScheme χ) (ha : IsSplitComponent a)
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hψK : ∀ g : rationalPoints G, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : rationalPoints G) * (k : rationalPoints G))
  (hψ'K : ∀ g : rationalPoints G, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : rationalPoints G) * (k : rationalPoints G))
  (hsq : SquaredModulusCompatibility (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
    (commonDecomposition χ ψ' hψ') (radical_isClosed ψ'))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

set_option hygiene false in
local notation "Ω" => pairFullDomainRegion χ K hK ψ hψ ψ' A

set_option maxHeartbeats 1200000 in
private theorem pairCompactRationalOn_of_presentation
    (d : ParabolicData χ ψ T a) (d' : ParabolicData χ ψ' T a)
    (pt : PresentationPointData (relativeWeylGroup d.r.data.i)
      ((SubgroupFunctor.range d.p).carrier (Over.mk (𝟙 _)))
      (parabolicLeviPointSubgroup d.p d.l)
      ((SubgroupFunctor.range (d.n ≫ d.p)).carrier (Over.mk (𝟙 _)))
      ((SubgroupFunctor.range d'.p).carrier (Over.mk (𝟙 _)))
      ((SubgroupFunctor.range (d'.n ≫ d'.p)).carrier (Over.mk (𝟙 _))) K)
    (hA : A.IsAdmissible) (hfin : A.HasFiniteLength)
    {D : Set (unramifiedCharacters (normCharacters χ))} (hDΩ : D ⊆ Ω) (hD : IsOpen D) :
    IsRationalOperatorOn D (restrictedCompactFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hsq A D hDΩ) := by
  let := hG.smooth
  let eP := parabolicPoints_eq χ ψ d.realizes
  let eP' := parabolicPoints_eq χ ψ' d'.realizes
  let eM := leviPoints_eq χ ψ d.realizes
  let eU := radicalPoints_eq χ ψ d.realizes
  let eU' := radicalPoints_eq χ ψ' d'.realizes
  let hδ := isUnimodularModulus_of_eq eU pt.radical_closed (radical_isClosed ψ)
    (radical_unimodular ψ hG)
  let hδ' := isUnimodularModulus_of_eq eU' pt.radical_closed' (radical_isClosed ψ')
    (radical_unimodular ψ' hG)
  have hsq₀ := squaredModulusCompatibility_ofEq eP.symm eM.symm eU.symm eP'.symm eU'.symm
    (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
    (commonDecomposition χ ψ' hψ') (radical_isClosed ψ')
    pt.decomposition pt.radical_closed pt.decomposition' pt.radical_closed' hsq
  let cc := characterComparison χ ψ d.r d.realizes
  let D₀ := cc.symm ⁻¹' D
  have hD₀ : IsOpen D₀ := hD.preimage cc.symm.continuous
  let A₀ := presentationRepresentation χ ψ d.realizes A
  let qMeasure := presentationQuotientMeasure χ ψ d.realizes K ψ' d'.realizes hK
  let ν₀ := parabolicLeviRationalNormCharacters d.r
  let isFull (w : unramifiedCharacters ν₀) : Prop :=
      domain pt.decomposition pt.radical_closed _
        (A₀.twist w.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν₀ w)) qMeasure = ⊤
  have hfullAt (z : Ω) : isFull (cc z.val) := by
    exact (domain_ofEq_eq_top_iff eP eM eU eU' pt.decomposition pt.radical_closed
      (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
      (A.twist (parameterTransport χ z.val).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z.val)))
      (pairQuotientMeasure K hK ψ ψ')).mpr z.property
  have hfull (w : D₀) : isFull w.val :=
    (congrArg isFull (cc.apply_symm_apply w.val)).mp (hfullAt ⟨cc.symm w.val, hDΩ w.property⟩)
  let c := transportedRationalUnramifiedCharacterCoordinates d.r.isCompatible.levi.isConnectedReductive
    (parabolicLeviPointHomeomorph d.r)
  have hdom := compactIntegralLocallyDominatedOn_of_isOpen_of_monomials
    pt.decomposition pt.radical_closed hδ K pt.parabolic_closed hK pt.factorization
    ν₀ (continuous_parabolicLeviRationalNormCharacters d.r) pt.projection_continuous
    A₀ _ qMeasure c.toHomeomorph (fun m => ⟨_, fun z =>
      transportedRationalUnramifiedCharacterCoordinates_apply_eval
        d.r.isCompatible.levi.isConnectedReductive (parabolicLeviPointHomeomorph d.r) z m⟩)
    hD₀ hfull
  have hrat := parabolicLevi_standardCompactRationalOn_of_dominated_of_finiteLength
    d.r d'.r (d.levi_comp.trans d'.levi_comp.symm) d.radical d'.radical rfl rfl rfl
    pt.decomposition pt.radical_closed hδ K pt.parabolic_closed hK pt.factorization
    pt.projection_continuous pt.decomposition' pt.radical_closed' hδ' pt.parabolic_closed'
    pt.factorization' pt.projection_continuous' qMeasure
    (presentationRadicalHaar χ K ψ' d'.realizes hK)
    (presentationIntersectionHaar χ ψ d.realizes K ψ' d'.realizes hK)
    (presentationQuotientMeasure_isCompatible χ ψ d.realizes K ψ' d'.realizes hK)
    hsq₀ A₀ (representationOfEq_isAdmissible' eM A hA)
    (representationOfEq_hasFiniteLength' eM A hfin) hD₀ hfull hdom
  let op (w : D₀) := sourceOperator χ ψ ψ' d.r d.realizes d'.realizes pt.decomposition
    pt.radical_closed pt.decomposition' pt.radical_closed' pt.parabolic_closed pt.parabolic_closed'
    K hK pt.factorization pt.factorization' pt.projection_continuous pt.projection_continuous'
    A hδ hδ' hsq₀ w.val (hfull w)
  have hrat' : IsRationalOperatorOn D₀ op := hrat
  have hratD := (isRationalOperatorOn_comparison_iff χ ψ d.r d.realizes D₀ op).mpr hrat'
  have hsub : D ⊆ cc ⁻¹' D₀ := by
    intro z hz
    change cc.symm (cc z) ∈ D
    rw [cc.symm_apply_apply]
    exact hz
  have hconj := ((hratD.restrict hsub).precomp
      (compactPictureComparison χ ψ hψ d.realizes pt.decomposition K A).toLinearEquiv.symm.toLinearMap).postcomp
    (targetPictureComparison χ ψ ψ' hψ' d.realizes d'.realizes pt.decomposition' K A).toLinearEquiv.toLinearMap
  have hop := operatorSquare hG χ ψ ψ' hψ hψ' d.r d.realizes d'.realizes
    pt.decomposition pt.radical_closed pt.decomposition' pt.radical_closed'
    pt.parabolic_closed pt.parabolic_closed' K hK pt.factorization pt.factorization'
    pt.projection_continuous pt.projection_continuous' hψK hψ'K A hδ hδ' hsq₀
  have hoperator :
      (fun z : D =>
        (targetPictureComparison χ ψ ψ' hψ' d.realizes d'.realizes pt.decomposition' K A).toLinearEquiv.toLinearMap ∘ₗ
          (op ⟨cc z.val, hsub z.property⟩ ∘ₗ
            (compactPictureComparison χ ψ hψ d.realizes pt.decomposition K A).toLinearEquiv.symm.toLinearMap)) =
      restrictedCompactFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hsq A D hDΩ := by
    funext z
    exact hop z.val (hDΩ z.property) (hfullAt ⟨z.val, hDΩ z.property⟩)
  rw [← hoperator]
  exact hconj

include ha in
/-- On any open subset of the full convergence domain, one regular denominator
clears the actual compact operator and is nonzero throughout the subset. -/
theorem pairCompactRationalOn_of_isOpen_subset
    (hA : A.IsAdmissible) (hfin : A.HasFiniteLength)
    {D : Set (unramifiedCharacters (normCharacters χ))} (hDΩ : D ⊆ Ω) (hD : IsOpen D) :
    IsRationalOperatorOn D (restrictedCompactFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hsq A D hDΩ) := by
  let d := parabolicData χ ψ hG hψ T a ha
  let d' := parabolicData χ ψ' hG hψ' T a ha
  let pt := presentationPointData F G hG χ ψ ψ' hψ hψ' T (parameterScheme χ)
    d.P d'.P d.U d'.U d.p d.l d'.p d'.l a d.n d'.n d.r d.realizes d'.realizes K hψK hψ'K
  exact pairCompactRationalOn_of_presentation hG χ ψ ψ' hψ hψ' a K hK hψK hψ'K hsq A
    d d' pt hA hfin hDΩ hD

include ha in
/-- If the actual full domain is open, the actual compact family admits a
common rational denominator nonzero at every parameter of that domain. -/
theorem pairCompactRationalOn_of_isOpen_fullDomain
    (hA : A.IsAdmissible) (hfin : A.HasFiniteLength) (hΩ : IsOpen Ω) :
    IsRationalOperatorOn Ω (compactFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hsq A) :=
  pairCompactRationalOn_of_isOpen_subset hG χ ψ ψ' hψ hψ' a ha K hK
    hψK hψ'K hsq A hA hfin subset_rfl hΩ

/-- A nonempty open actual full domain gives continuation data for that
entire domain, with its original quotient measure. -/
def pairContinuationOfOpenFullDomain
    (hA : A.IsAdmissible) (hfin : A.HasFiniteLength) (hΩ : IsOpen Ω) (hne : Set.Nonempty Ω) :
    RationalOperatorContinuationData Ω (compactFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hsq A) :=
  rationalOperatorContinuation (parameterScheme χ) (parameterProjection_continuous χ)
    (parameterScheme_isConnectedReductive χ hG) hΩ hne subset_rfl _
    (pairCompactRationalOn_of_isOpen_fullDomain hG χ ψ ψ' hψ hψ' a ha K hK
      hψK hψ'K hsq A hA hfin hΩ)

section Opposite

variable (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (hPK : ∀ g : rationalPoints G, ∃ p : parabolic χ, ∃ k : K,
    g = (p : rationalPoints G) * (k : rationalPoints G))
  (hOppK : ∀ g : rationalPoints G, ∃ p : oppositeParabolic χ, ∃ k : K,
    g = (p : rationalPoints G) * (k : rationalPoints G))

/-- The actual forward continuation, under openness and nonemptiness of
its full convergence domain. -/
def forwardContinuationOfOpenFullDomain
    (hA : A.IsAdmissible) (hfin : A.HasFiniteLength)
    (hΩ : IsOpen (forwardFullDomainRegion χ K hK A))
    (hne : (forwardFullDomainRegion χ K hK A).Nonempty) :
    ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A :=
  pairContinuationOfOpenFullDomain hG χ χ (Dynamic.inverseCocharacter χ) rfl
    (Dynamic.centralizer_inverseCocharacter χ) a ha K hK hPK hOppK
    (conditionalSquaredModulus χ hRefl hCST hG) A hA hfin hΩ hne

/-- The actual reverse continuation at the same compact and Haar scale,
under openness and nonemptiness of its full convergence domain. -/
def reverseContinuationOfOpenFullDomain
    (hA : A.IsAdmissible) (hfin : A.HasFiniteLength)
    (hΩ : IsOpen (reverseFullDomainRegion χ K hK A))
    (hne : (reverseFullDomainRegion χ K hK A).Nonempty) :
    ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A :=
  pairContinuationOfOpenFullDomain hG χ (Dynamic.inverseCocharacter χ) χ
    (Dynamic.centralizer_inverseCocharacter χ) rfl a ha K hK hOppK hPK
    (conditionalReverseSquaredModulus χ hRefl hCST hG) A hA hfin hΩ hne

end Opposite

end Langlands.Plancherel.DynamicCommonLeviContinuation
