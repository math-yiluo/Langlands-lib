import Langlands.Representation.Plancherel.ActualCommonLeviTestAverage
import Langlands.Representation.Plancherel.ActualCommonLeviNonvanishing
import Langlands.Representation.Plancherel.DynamicOppositeDualAdjunctionProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchurOrthogonality

/-! # A fixed pair of compact test sections for common-Levi adjunction -/

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option quotPrecheck false

universe u uV

open CategoryTheory AlgebraicGeometry Filter MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj ENNReal NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviIwasawa

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicOppositeNonvanishing DynamicCommonLeviComposition DynamicCommonLeviCompact
open ActualCommonLeviTensor OppositeIntertwiningDualAdjunction StandardIntertwining.OrderedSubgroupFactorization

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

section Support

variable {X : Type u} [Group X] [TopologicalSpace X]
  [LocallyCompactSpace X] [NonarchimedeanGroup X]
  {P P' M U V : Subgroup X} (d : IsSemidirectDecomposition P M U) (Q : OpenSubgroup X)

omit [LocallyCompactSpace X] [NonarchimedeanGroup X] in
private theorem commonTestSupport (d : IsSemidirectDecomposition P M U)
    (d' : IsSemidirectDecomposition P' M V) (Q : OpenSubgroup X)
    (hloc : HasSourceLocalProduct P U V Q)
    {g : X} (hg : ∃ p ∈ P, ∃ k ∈ Q, g = p * k)
    (hg' : ∃ p ∈ P', ∃ k ∈ Q, g = p * k) :
    ∃ (m : M) (x : U.subgroupOf V) (q : Q), g = (m : X) * intersectionAmbientHom U V x * q := by
  obtain ⟨a, ha, b, hb, hab⟩ := hg
  obtain ⟨p, hp, q, hq, hpq⟩ := hg'
  let m := d'.projection ⟨p, hp⟩
  let v : V := ⟨(m : X)⁻¹ * p, d'.projection_inv_mul_mem ⟨p, hp⟩⟩
  have hp₁ : p = a * b * q⁻¹ := by rw [← hab, hpq, mul_inv_cancel_right]
  have hv : (v : X) = ((m : X)⁻¹ * a) * (b * q⁻¹) := by
    change (m : X)⁻¹ * p = _
    rw [hp₁]
    group
  obtain ⟨x, hx, y, hy, hyV, he⟩ := hloc v v.property
    ⟨_, mul_mem (inv_mem (d.levi_le m.property)) ha, _, Q.mul_mem hb (Q.inv_mem hq), hv⟩
  have hxV : x ∈ V := by
    have hh : (v : X) * y⁻¹ ∈ V := mul_mem v.property (inv_mem hyV)
    rwa [he, mul_inv_cancel_right] at hh
  refine ⟨m, ⟨⟨x, hxV⟩, hx⟩, ⟨y * q, Q.mul_mem hy hq⟩, ?_⟩
  change g = (m : X) * x * (y * q)
  calc
    g = p * q := hpq
    _ = (m : X) * (v : X) * q := by
      change p * q = (m : X) * ((m : X)⁻¹ * p) * q
      group
    _ = _ := by
      rw [he]
      group

private theorem sourceTestVector_eval_levi_unipotent (hU : IsClosed (U : Set X))
    (T : SmoothRep.{0, u, uV} ℂ M) (hQ : IsCompact (Q : Set X)) (v : T)
    (hv : v ∈ fixedVectors (leviInflatedInducingRepresentation d hU T)
      (conjOpenSubgroup P Q 1).toSubgroup) (m : M) (x : U) (q : Q) :
    eval P (leviInflatedInducingRepresentation d hU T) (sourceTestVector d hU T Q hQ v hv)
        ((m : X) * (x : X) * (q : X)) =
      (HaarModulus.closedHalfCharacter U hU M d.levi_le_normalizer m : ℂ) • T.representation m v := by
  let p : P := ⟨m, d.levi_le m.property⟩ * ⟨x, d.unipotent_le x.property⟩
  have hp : d.projection p = m := d.projection_mul m x
  change eval P (leviInflatedInducingRepresentation d hU T) (sourceTestVector d hU T Q hQ v hv)
    ((p : X) * (q : X)) = _
  rw [sourceTestVector_eval_mul]
  change (HaarModulus.closedHalfCharacter U hU M d.levi_le_normalizer (d.projection p) : ℂ) •
    T.representation (d.projection p) v = _
  rw [hp]

private theorem dualIntegrand_eq_zero_of_eval_zero (hU : IsClosed (U : Set X))
    (d' : IsSemidirectDecomposition P' M V) (hV : IsClosed (V : Set X))
    {T : SmoothRep.{0, u, uV} ℂ M}
    {ξ ξ' : M →* ℂˣ} {hξ : IsOpen (ξ.ker : Set M)} {hξ' : IsOpen (ξ'.ker : Set M)}
    (f : (DynamicNormalization.leviTwistedInductionFunctor d hU).obj (T.twist ξ hξ))
    (f' : (DynamicNormalization.leviTwistedInductionFunctor d' hV).obj
      (T.contragredient.twist ξ' hξ'))
    (g : X)
    (hz : eval P (leviInflatedInducingRepresentation d hU (T.twist ξ hξ)) f g = 0 ∨
      eval P' (leviInflatedInducingRepresentation d' hV (T.contragredient.twist ξ' hξ')) f' g = 0) :
    dualIntegrand d hU d' hV f f' g = 0 := by
  unfold dualIntegrand
  rcases hz with hz | hz
  · rw [hz]
    exact (smoothDualPairing T.representation
      (eval P' (leviInflatedInducingRepresentation d' hV (T.contragredient.twist ξ' hξ')) f' g)).map_zero
  · rw [hz, map_zero]

end Support

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

local notation "Γ" => RationalPoint F G.X
local notation "h₀" => commonDecomposition χ ψ hψ
local notation "h₁" => commonDecomposition χ ψ' hψ'
local notation "hU₀" => radical_isClosed ψ
local notation "hU₁" => radical_isClosed ψ'
local notation "hP₀" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ
local notation "hP₁" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ'
local notation "hr₀" => commonProjection_continuous χ ψ hψ
local notation "hr₁" => commonProjection_continuous χ ψ' hψ'
local notation "ν" => leviNormCharacters χ
local notation "hν" => (fun a => (DynamicOppositeCanonicalScalar.normCharacters_continuous χ a).comp
  (parameterHomeomorph χ).symm.continuous)
local notation "I" => (radical ψ).subgroupOf (radical ψ')
local notation "incl" => intersectionAmbientHom (radical ψ) (radical ψ')

/-- Common compact support and paired inducing values for the two adjunction tests. -/
structure CompactAdjunctionTest where
  subgroup : OpenSubgroup Γ
  isCompact_subgroup : IsCompact (subgroup : Set Γ)
  subgroup_le : (subgroup : Set Γ) ⊆ K
  localProduct : HasSourceLocalProduct (parabolic ψ) (radical ψ) (radical ψ') subgroup
  vector : A
  functional : A.contragredient
  pairing : functional.val vector = 1
  sourceFixed : vector ∈ fixedVectors (A.representation.comp (h₀).projection)
    (conjOpenSubgroup (parabolic ψ) subgroup 1).toSubgroup
  targetFixed : functional ∈ fixedVectors (A.contragredient.representation.comp (h₁).projection)
    (conjOpenSubgroup (parabolic ψ') subgroup 1).toSubgroup

/-- Choose a single pair of fixed test vectors detecting the exact adjunction scale. -/
def chooseCompactAdjunctionTest (hG : IsConnectedReductive G) [Nontrivial A] :
    CompactAdjunctionTest χ K ψ hψ ψ' hψ' A :=
  Classical.choice (by
    obtain ⟨v, hv⟩ := exists_ne (0 : A)
    obtain ⟨ℓ, hℓ⟩ := HarishChandraSchwartz.exists_smoothDual_eq_one
      (compactOpenCofinal_of_isClosed (levi_isClosed χ)) A.isSmooth hv
    obtain ⟨S, hS⟩ := A.isSmooth v
    obtain ⟨S', hS'⟩ := A.contragredient.isSmooth ℓ
    obtain ⟨W, hW, hw⟩ := exists_nhds_fixedVectors_comp_projection h₀ hr₀ A.representation S v hS
    obtain ⟨W', hW', hw'⟩ := exists_nhds_fixedVectors_comp_projection h₁ hr₁
      A.contragredient.representation S' ℓ hS'
    obtain ⟨Q, hQc, hQ, hloc⟩ := exists_factored_compactOpen_subset ψ hG
      (inter_mem (inter_mem hW hW') (K.isOpen.mem_nhds K.one_mem))
    exact ⟨⟨Q, hQc, fun x hx => (hQ hx).2,
      hasSourceLocalProduct_of_commonCentralizer χ hG ψ hψ ψ' hψ' Q hloc,
      v, ℓ, hℓ, hw Q (fun x hx => (hQ hx).1.1), hw' Q (fun x hx => (hQ hx).1.2)⟩⟩)

variable (t : CompactAdjunctionTest χ K ψ hψ ψ' hψ' A)
  (z : unramifiedCharacters (normCharacters χ))

local notation "η" => parameterTransport χ z
local notation "η'" => parameterTransport χ z⁻¹
local notation "Az" => twistObject χ z A
local notation "Ad" => twistObject χ z⁻¹ A.contragredient
local notation "hv" =>
  mem_fixedVectors_twist h₀ hU₀ hP₀ t.subgroup t.isCompact_subgroup hr₀ ν hν A
    (fun _ hx => hx) t.sourceFixed η
local notation "hℓ" =>
  mem_fixedVectors_twist h₁ hU₁ hP₁ t.subgroup t.isCompact_subgroup hr₁ ν hν A.contragredient
    (fun _ hx => hx) t.targetFixed η'

/-- On the source, the compact test section in the actual parameter twist. -/
def sourceAdjunctionTestSection : UnramifiedLeviInduction h₀ hU₀ ν η A :=
  sourceTestVector h₀ hU₀ Az t.subgroup t.isCompact_subgroup t.vector hv

/-- On the target, the compact test section of the inverse twist of the smooth dual. -/
def targetAdjunctionTestSection : UnramifiedLeviInduction h₁ hU₁ ν η' A.contragredient :=
  sourceTestVector h₁ hU₁ Ad t.subgroup t.isCompact_subgroup t.functional hℓ

local notation "f" => sourceAdjunctionTestSection χ K ψ hψ ψ' hψ' A t z
local notation "f'" => targetAdjunctionTestSection χ K ψ hψ ψ' hψ' A t z
local notation "Θ" => dualIntegrand h₀ hU₀ h₁ hU₁ f f'

local instance testSectionsAmbientMeasurable : MeasurableSpace Γ := borel _
local instance testSectionsAmbientBorel : BorelSpace Γ := ⟨rfl⟩
attribute [local instance] Langlands.HaarModulus.subgroupMeasurableSpace Langlands.HaarModulus.subgroupBorelSpace

private theorem dualIntegrand_testSections_factor
    (hCompact : IsCompact (K : Set Γ)) (hG : IsConnectedReductive G)
    (hδ : SquaredModulusCompatibility h₀ hU₀ h₁ hU₁)
    (m : levi χ) (x : I) (q : t.subgroup) :
    Θ ((m : Γ) * incl x * (q : Γ)) =
      ((normalizedTestAverage χ K hCompact t.subgroup ψ ψ' ((m : Γ) * incl x * (q : Γ))).toReal : ℂ) := by
  let u : radical ψ := ⟨incl x, x.property⟩
  let u' : radical ψ' := x.val
  let a := (HaarModulus.closedHalfCharacter (radical ψ) hU₀ (levi χ) (h₀).levi_le_normalizer m : ℂ)
  let b := (HaarModulus.closedHalfCharacter (radical ψ') hU₁ (levi χ) (h₁).levi_le_normalizer m : ℂ)
  have e₀ : eval (parabolic ψ) (leviInflatedInducingRepresentation h₀ hU₀ Az) f
      ((m : Γ) * incl x * (q : Γ)) = a • (Az).representation m t.vector :=
    sourceTestVector_eval_levi_unipotent h₀ t.subgroup hU₀ Az t.isCompact_subgroup t.vector hv m u q
  have e₁ : eval (parabolic ψ') (leviInflatedInducingRepresentation h₁ hU₁ Ad) f'
      ((m : Γ) * incl x * (q : Γ)) = b • (Ad).representation m t.functional :=
    sourceTestVector_eval_levi_unipotent h₁ t.subgroup hU₁ Ad t.isCompact_subgroup t.functional hℓ m u' q
  unfold dualIntegrand
  rw [e₀, e₁, twistEvaluationFunctional_twist_apply]
  have hpair : (twistEvaluationFunctional (A := A) (η').val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν η') t.vector).val t.functional = 1 := t.pairing
  have hchar : ((η).val.toMonoidHom m : ℂ) * ((η').val.toMonoidHom m : ℂ) = 1 :=
    DynamicOppositeDualAdjunctionProof.parameterTransport_mul_inv χ z m
  rw [hpair, mul_one, mul_mul_mul_comm, hchar, mul_one,
    normalizedTestAverage_factor χ K hCompact t.subgroup ψ ψ' hψ hψ' hG t.isCompact_subgroup m x q]
  let : LocallyCompactSpace (radical ψ') := (hU₁).locallyCompactSpace
  let : LocallyCompactSpace I :=
    ((hU₀).preimage (continuous_subtype_val : Continuous (Subtype.val : radical ψ' → Γ))).locallyCompactSpace
  let c := mulEquivHaarChar (intersectionConj χ ψ ψ' hψ hψ' m)
  let d₀ := (HaarModulus.closedRestrictCharacter (radical ψ) hU₀ (levi χ)
    (h₀).levi_le_normalizer m : ℝ≥0)
  let d₁ := (HaarModulus.closedRestrictCharacter (radical ψ') hU₁ (levi χ)
    (h₁).levi_le_normalizer m : ℝ≥0)
  have hs : d₀ * d₁ = c ^ 2 := hδ m
  have hroot : NNReal.sqrt d₀ * NNReal.sqrt d₁ = c := by
    rw [← NNReal.sqrt_mul, hs, NNReal.sqrt_sq]
  change ((NNReal.sqrt d₀ : ℝ) : ℂ) * ((NNReal.sqrt d₁ : ℝ) : ℂ) = (((c : ℝ≥0∞).toReal : ℝ) : ℂ)
  rw [ENNReal.coe_toReal, ← Complex.ofReal_mul, ← NNReal.coe_mul, hroot]

/-- The pairing of the actual test sections is the common normalized average. -/
theorem dualIntegrand_testSections_eq (hCompact : IsCompact (K : Set Γ)) (hG : IsConnectedReductive G)
    (hδ : SquaredModulusCompatibility h₀ hU₀ h₁ hU₁) (g : Γ) :
    Θ g = ((normalizedTestAverage χ K hCompact t.subgroup ψ ψ' g).toReal : ℂ) := by
  by_cases hg : ∃ (m : levi χ) (x : I) (q : t.subgroup), g = (m : Γ) * incl x * (q : Γ)
  · obtain ⟨m, x, q, rfl⟩ := hg
    exact dualIntegrand_testSections_factor χ K ψ hψ ψ' hψ' A t z hCompact hG hδ m x q
  · rw [normalizedTestAverage_eq_zero χ K hCompact t.subgroup ψ ψ' hψ hψ' hg,
      ENNReal.toReal_zero, Complex.ofReal_zero]
    refine dualIntegrand_eq_zero_of_eval_zero h₀ hU₀ h₁ hU₁ f f' g ?_
    by_cases hf : ∃ p ∈ parabolic ψ, ∃ k ∈ t.subgroup, g = p * k
    · have hf' : ¬∃ p ∈ parabolic ψ', ∃ k ∈ t.subgroup, g = p * k := fun hh =>
        hg (commonTestSupport h₀ h₁ t.subgroup t.localProduct hf hh)
      exact Or.inr
        (sourceTestVector_eval_eq_zero h₁ hU₁ Ad t.subgroup t.isCompact_subgroup t.functional hℓ g hf')
    · exact Or.inl
        (sourceTestVector_eval_eq_zero h₀ hU₀ Az t.subgroup t.isCompact_subgroup t.vector hv g hf)

end Langlands.Plancherel.ActualCommonLeviIwasawa
