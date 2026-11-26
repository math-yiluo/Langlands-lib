import Langlands.Representation.Plancherel.ActualOppositeFullDomainContinuationStatement
import Langlands.Representation.Plancherel.ActualCommonLeviUnitaryContinuation
import Langlands.Representation.Plancherel.DynamicCommonLeviClearedOperator
import Langlands.Representation.Plancherel.DynamicCommonLeviPQDiscriminant
import Langlands.Representation.Plancherel.DynamicOppositeGalleryComparison
import Langlands.Representation.Plancherel.ParabolicPointUniformNumerator
import Langlands.Representation.Plancherel.RationalFullDomainContinuation
import Langlands.Representation.Plancherel.StandardCompactUnitaryConvergence
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SquareIntegrableSemisimplicity

/-! # Whole-domain continuations of the actual opposite standard integrals -/

noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option quotPrecheck false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Topology
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

open Aubert.General Induction StandardIntertwining UnramifiedOperatorFamily
open DynamicOppositeCanonicalScalar DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open DynamicCommonLeviPresentations ActualCommonLeviV3 ActualCommonLeviTensor

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
  DynamicCommonLeviContinuation.radicalMeasurable
  DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable
  DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable
  DynamicCommonLeviContinuation.quotientBorel
  ActualCommonLeviV3.leviLocallyCompact

section Pair

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (hG : IsConnectedReductive G)
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : rationalPoints G, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : rationalPoints G) * (k : rationalPoints G))
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : rationalPoints G, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : rationalPoints G) * (k : rationalPoints G))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

set_option hygiene false in
local notation "Ω" => pairFullDomainRegion χ K hK ψ hψ ψ' A
local notation "h₀" => commonDecomposition χ ψ hψ
local notation "h₁" => commonDecomposition χ ψ' hψ'
local notation "hU₀" => radical_isClosed ψ
local notation "hU₁" => radical_isClosed ψ'
local notation "hδ₀" => radical_unimodular ψ hG
local notation "hδ₁" => radical_unimodular ψ' hG
local notation "hP₀" => parabolic_isClosed ψ
local notation "hP₁" => parabolic_isClosed ψ'
local notation "hr₀" => commonProjection_continuous χ ψ hψ
local notation "hr₁" => commonProjection_continuous χ ψ' hψ'
local notation "L" => parameterScheme χ
local notation "hL" => parameterScheme_isConnectedReductive χ hG
local notation "ν" => normCharacters χ
local notation "νM" => leviNormCharacters χ
local notation "hνM" => fun i => (normCharacters_continuous χ i).comp (parameterHomeomorph χ).symm.continuous
local notation "X" => unramifiedCharacters ν
local notation "Xu" => unitaryUnramifiedCharacters ν
local notation "R" => unramifiedRegularFunctions ν
local notation "qν" => pairQuotientMeasure K hK ψ ψ'
local notation "μU" => radicalHaar ψ' K hK
local notation "μI" => pairIntersectionHaar K hK ψ ψ'
local notation "hμ" => pairQuotientMeasure_isCompatible K hK ψ ψ'
local notation "hM" => levi_isClosed χ
local notation "χM" => parameterTransport χ
local notation "Aχ" => fun (w : unramifiedCharacters νM) =>
  A.twist w.val.toMonoidHom (unramifiedCharacter_isOpen_ker νM w)

variable (hsq : SquaredModulusCompatibility (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
  (commonDecomposition χ ψ' hψ') (radical_isClosed ψ'))

local notation "J" => compactFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hsq A

private theorem pairFullDomain_uniform_numerator (hadm : A.IsAdmissible) (hfin : A.HasFiniteLength) :
    ∃ b : R, b ≠ 0 ∧ IsPolynomialOperatorOn Ω (fun z => b.val z.val • J z) := by
  let := hG.smooth
  let := hG.isSeparated
  have : LocallyCompactSpace (radical ψ') := (hU₁).isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨g, _, hb⟩ := exists_dynamic_oppositeIwahoriContractionBasis (k := F) (G := G) ψ
  obtain ⟨a, _, ha⟩ := exists_dynamic_oppositeIwahoriContractionBasis (k := F) (G := G) ψ'
  change Jacquet.HasOppositeIwahoriContractionBasis (radical ψ) (levi ψ) (oppositeRadical ψ) g at hb
  change Jacquet.HasOppositeIwahoriContractionBasis (radical ψ') (levi ψ') (oppositeRadical ψ') a at ha
  have hψM : levi ψ = levi χ := by simp only [levi, hψ]
  have hψ'M : levi ψ' = levi χ := by simp only [levi, hψ']
  rw [hψM] at hb
  rw [hψ'M] at ha
  have hnorm : levi χ ≤ Subgroup.normalizer (oppositeRadical ψ : Set (rationalPoints G)) := by
    rw [← hψM]
    change (Dynamic.centralizer ψ).carrier (Over.mk (𝟙 _)) ≤
      Subgroup.normalizer (((Dynamic.unipotent (Dynamic.inverseCocharacter ψ)).carrier
        (Over.mk (𝟙 _)) : Subgroup (rationalPoints G)) : Set (rationalPoints G))
    rw [← Dynamic.centralizer_inverseCocharacter ψ]
    exact Dynamic.centralizer_le_normalizer_unipotent _ _
  have hint : ∀ x : rationalPoints G, x ∈ parabolic ψ → x ∈ oppositeRadical ψ → x = 1 :=
    fun _ hp hu => Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic ψ hu hp
  let Ξ := (χM).symm ⁻¹' Ω
  have hfull (z : Ξ) : domain h₀ hU₀ (radical ψ') (Aχ z.val) qν = ⊤ := by
    have hz : domain h₀ hU₀ (radical ψ') (Aχ (χM ((χM).symm z.val))) qν = ⊤ := z.property
    exact (congrArg (fun w => domain h₀ hU₀ (radical ψ') (Aχ w) qν = ⊤)
      ((χM).apply_symm_apply z.val)).mp hz
  obtain ⟨b, hb, hpoly⟩ := exists_uniform_standardCompactOperator_numerator
    h₀ hU₀ hδ₀ K hP₀ hK hψK νM hνM hr₀ A h₁ hU₁ hδ₁ hP₁ hψ'K hr₁ qν μU μI hμ hM hsq
    hnorm hint g hb a ha hadm hfin Ξ hfull
  let e := unramifiedRegularFunctionsEquiv (parameterHomeomorph χ) ν
  refine ⟨e.symm b, fun he => hb (e.symm.injective (he.trans (map_zero e.symm).symm)), ?_⟩
  have hsub : Ω ⊆ χM ⁻¹' Ξ := by
    intro z hz
    change (χM).symm (χM z) ∈ Ω
    rw [ContinuousMulEquiv.symm_apply_apply]
    exact hz
  have htransport := (isPolynomialOperatorOn_transport_iff (parameterHomeomorph χ) ν Ξ _).mpr hpoly
  intro f
  exact (htransport f).restrict hsub

omit [LocallyOfFiniteType G.X.hom] in
private theorem parameter_norm_unitary_mul (τ : X) (z : Xu) (m : levi χ) :
    ‖((χM (τ * unitaryToUnramified L z)).val m : ℂ)‖ = ‖((χM τ).val m : ℂ)‖ := by
  rw [map_mul]
  change ‖((χM τ).val m : ℂ) * (z.val ((parameterHomeomorph χ).symm m) : ℂ)‖ = _
  rw [norm_mul, z.property.2 ((parameterHomeomorph χ).symm m), mul_one]

include hG hψK hψ' hsq in
private theorem pairFullDomain_unitary_mul (hadm : A.IsAdmissible) (τ : Ω) (z : Xu) :
    τ.val * unitaryToUnramified L z ∈ Ω := by
  exact standardCompactFullDomain_of_character_norm_eq h₀ hU₀ hδ₀ K hP₀ hK hψK νM hνM hr₀ A
    h₁ hU₁ qν μU μI hμ hM hsq hadm (χM τ.val) (χM (τ.val * unitaryToUnramified L z))
    (fun m => (parameter_norm_unitary_mul χ τ.val z m).symm) τ.property

private theorem pairFullDomain_scalarContinuous (hadm : A.IsAdmissible) (τ : Ω)
    (v : CompactInductionPicture h₀ K A) (i : K × SmoothDual A.representation) :
    Continuous (fun z : Xu => compactPictureScalarTests h₁ K A i
      (J ⟨τ.val * unitaryToUnramified L z,
        pairFullDomain_unitary_mul χ hG K hK ψ hψ hψK ψ' hψ' A hsq hadm τ z⟩ v)) := by
  let c (z : Xu) := χM (τ.val * unitaryToUnramified L z)
  have hc : Continuous c := (χM).continuous.comp (continuous_const.mul
    (continuous_subtype_val.subtype_mk (fun w : Xu => w.property.1)))
  let : FirstCountableTopology Circle := IsEmbedding.subtypeVal.firstCountableTopology
  let : FirstCountableTopology Xu :=
    (rationalCanonicalUnitaryUnramifiedCharacterCoordinates L hL).toHomeomorph.isEmbedding.firstCountableTopology
  have hd (z : Xu) : domain h₀ hU₀ (radical ψ') (Aχ (c z)) qν = ⊤ :=
    pairFullDomain_unitary_mul χ hG K hK ψ hψ hψK ψ' hψ' A hsq hadm τ z
  exact continuous_standardCompactOperator_scalar_of_character_norm_eq
    h₀ hU₀ hδ₀ K hP₀ hK hψK νM hνM hr₀ A h₁ hU₁ qν μU μI hμ hM hsq hδ₁ hP₁ hψ'K hr₁
    c hc (χM τ.val) (parameter_norm_unitary_mul χ τ.val) τ.property hd v i.1 i.2

local notation "first" => (⟨ψ, hψ⟩ : GalleryVertex χ)
local notation "last" => (⟨ψ', hψ'⟩ : GalleryVertex χ)
local notation "OpenPair" => ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (ha : IsSplitComponent a)

include ha in
private theorem translatedClearedPair_zeroFibers (hadm : A.IsAdmissible) (hi : A.IsIrreducible)
    (p : OpenPair) (τ : X) : ∃ b : R, Nonempty (RationalUnitaryPoleFactorization L b) ∧
      ∀ (q : PairContinuation χ hG K hK ψ hψ hψK ψ' hψ' hψ'K p.modulus A
        p.region p.converges) (z : X),
        b.val z ≠ 0 → q.denominator.val (τ * z) = 0 → q.numerator (τ * z) = 0 := by
  let σ := SmoothRep.pullback (parameterHomeomorph χ) A
  let σ₀ := σ.twist τ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν τ)
  have hσ : σ.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff A.representation (parameterHomeomorph χ)).mpr hi
  have hσadm : σ.IsAdmissible := isAdmissible_comp_continuousMulEquiv A.representation
    (parameterHomeomorph χ) hadm
  have hσ₀ : σ₀.IsIrreducible := (isIrreducible_twist_iff τ.val.toMonoidHom σ.representation).mpr hσ
  have hσ₀adm : σ₀.IsAdmissible := (isAdmissible_twist_iff τ.val.toMonoidHom σ.representation
    (unramifiedCharacter_isOpen_ker ν τ)).mpr hσadm
  let b := galleryPQDiscriminant hG ha first last σ₀ hσ₀ hσ₀adm
  refine ⟨b.scalar, ⟨b.factors⟩, fun q z hz hzero => ?_⟩
  have he : σ₀.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z) =
      σ.twist (τ * z).val.toMonoidHom (unramifiedCharacter_isOpen_ker ν (τ * z)) := by
    apply CategoryTheory.ObjectProperty.FullSubcategory.ext
    have hrepr : (σ₀.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z)).representation =
        (σ.twist (z * τ).val.toMonoidHom (unramifiedCharacter_isOpen_ker ν (z * τ))).representation :=
      Langlands.twist_twist z.val.toMonoidHom τ.val.toMonoidHom σ.representation
    exact (congrArg Rep.of hrepr).trans (congrArg (fun w : X =>
      (σ.twist w.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν w)).obj) (mul_comm z τ))
  have hTwist := intrinsicGalleryCoefficient_twist χ A (τ * z)
  exact compactPairNumerator_eq_zero_of_PQRegular hG ha K hK first last hψK hψ'K A p q
    (τ * z) (hTwist.symm ▸ (he ▸ b.regular z hz)) hzero

include ha in
private theorem pairFullDomain_continuation (hadm : A.IsAdmissible) (hi : A.IsIrreducible) (p : OpenPair) :
    Nonempty (RationalOperatorContinuationData Ω
      (compactFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K p.modulus A)) := by
  obtain ⟨b, hb, hpoly⟩ := pairFullDomain_uniform_numerator χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A
    p.modulus hadm (SmoothRep.hasFiniteLength_of_isIrreducible hi)
  exact nonempty_fullDomainContinuation_of_unitary_translates L hL _ p.converges
    p.isOpen_region p.nonempty_region
    (pairFullDomain_unitary_mul χ hG K hK ψ hψ hψK ψ' hψ' A p.modulus hadm)
    (compactPictureScalarTests h₁ K A) (compactPictureScalarTests_separates h₁ K A hM)
    (pairFullDomain_scalarContinuous χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p.modulus hadm)
    p.presentation b hb hpoly
    (fun τ => translatedClearedPair_zeroFibers χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A ha hadm hi p τ.val)

end Pair

/-- The actual forward and reverse operators admit one clearing denominator
apiece, each nonvanishing on the corresponding entire convergence domain. -/
theorem actualOppositeFullDomainContinuation : ActualOppositeFullDomainContinuationStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ χ hG K hK hPK hOppK A hi C _ hC _ _ mu _ _ hsq
  have hunit := HarishChandraSchwartz.isUnitarizable_of_isSquareIntegrableModCentralSubgroup
    C hC mu (compactOpenCofinal_of_nonarchimedean (levi χ)) hsq
  have hfin := SmoothRep.hasFiniteLength_of_isIrreducible hi
  obtain ⟨T, a, ha⟩ := (splitComponentStatement F (parameterScheme χ)
    (parameterScheme_isConnectedReductive χ hG)).1
  let hOpp := Dynamic.centralizer_inverseCocharacter χ
  let f := continuedPairOfUnitarizable χ hG K hK χ rfl hPK
    (Dynamic.inverseCocharacter χ) hOpp hOppK A hsq.1 hfin hunit
  let r := continuedPairOfUnitarizable χ hG K hK (Dynamic.inverseCocharacter χ) hOpp hOppK
    χ rfl hPK A hsq.1 hfin hunit
  exact ⟨⟨pairFullDomain_continuation χ hG K hK χ rfl hPK (Dynamic.inverseCocharacter χ)
      hOpp hOppK A ha hsq.1 hi f, ⟨f.region, f.isOpen_region, f.nonempty_region, f.converges⟩⟩,
    ⟨pairFullDomain_continuation χ hG K hK (Dynamic.inverseCocharacter χ) hOpp hOppK χ rfl
      hPK A ha hsq.1 hi r, ⟨r.region, r.isOpen_region, r.nonempty_region, r.converges⟩⟩⟩

end Langlands.Plancherel
