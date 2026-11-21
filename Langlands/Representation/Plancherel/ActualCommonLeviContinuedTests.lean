import Langlands.Representation.Plancherel.ActualCommonLeviTestPairing
import Langlands.Representation.Plancherel.DynamicOppositeContragredientScalarReduction

/-! # Exact tests of the compact continued common-Levi operators -/

noncomputable section

set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option quotPrecheck false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj ENNReal NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviIwasawa

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor

section CompactIntegral

variable {X : Type u} [Group X] [TopologicalSpace X]
  [NonarchimedeanGroup X] [MeasurableSpace X] [BorelSpace X]
  {P M U : Subgroup X} (h : IsSemidirectDecomposition P M U)
  (K : OpenSubgroup X) (hK : IsCompact (K : Set X))
  (A : SmoothRep.{0, u, uV} ℂ M)
  (φ : CompactInductionPicture h K A) (φ' : CompactInductionPicture h K A.contragredient)
  (f : X → A) (f' : X → A.contragredient)

private theorem compactPictureDualPairing_eq_setIntegral
    (hf : ∀ k : K, eval _ _ φ k = f (k : X))
    (hf' : ∀ k : K, eval _ _ φ' k = f' (k : X)) :
    compactPictureDualPairing h K hK A φ φ' =
      ∫ x in (K : Set X), smoothDualPairing A.representation (f' x) (f x)
        ∂(RankinSelberg.normalizedCompactOpenHaar K hK) := by
  unfold compactPictureDualPairing CompactInduction.measure
  calc
    _ = ∫ k : K, smoothDualPairing A.representation (f' (k : X)) (f (k : X))
        ∂(RankinSelberg.normalizedCompactOpenHaar K hK).comap Subtype.val := by
      refine integral_congr_ae (ae_of_all _ fun k => ?_)
      exact congrArg₂ (fun ℓ v => smoothDualPairing A.representation ℓ v) (hf' k) (hf k)
    _ = _ := integral_subtype_comap K.isOpen.measurableSet
      (fun x => smoothDualPairing A.representation (f' x) (f x))

end CompactIntegral

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
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  Langlands.HaarModulus.subgroupMeasurableSpace
  Langlands.HaarModulus.subgroupBorelSpace
  DynamicCommonLeviContinuation.quotientMeasurable
  DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance continuedTestsAmbientMeasurable : MeasurableSpace (RationalPoint F G.X) := borel _
local instance continuedTestsAmbientBorel : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
local instance continuedTestsAmbientSecondCountable : SecondCountableTopology (RationalPoint F G.X) :=
  Langlands.AlgebraicGeometry.PointTopology.rationalPoint_secondCountableTopology F G
local instance continuedTestsSubgroupSecondCountable (S : Subgroup (RationalPoint F G.X)) : SecondCountableTopology S :=
  TopologicalSpace.Subtype.secondCountableTopology (S : Set (RationalPoint F G.X))
local instance continuedTestsRadicalLocallyCompact (φ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    LocallyCompactSpace (radical φ) := (radical_isClosed φ).locallyCompactSpace
local instance continuedTestsLeviLocallyCompact (φ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    LocallyCompactSpace (levi φ) := (levi_isClosed φ).locallyCompactSpace
local instance continuedTestsIntersectionLocallyCompact (ψ φ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    LocallyCompactSpace ((radical ψ).subgroupOf (radical φ)) :=
  ((radical_isClosed ψ).preimage continuous_subtype_val).locallyCompactSpace
local instance continuedTestsIntersectionSecondCountable (ψ φ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    SecondCountableTopology ((radical ψ).subgroupOf (radical φ)) :=
  TopologicalSpace.Subtype.secondCountableTopology
    ((radical ψ).subgroupOf (radical φ) : Set (radical φ))

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (t : CompactAdjunctionTest χ K ψ hψ ψ' hψ' A)

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
local notation "Z" => unramifiedCharacters (normCharacters χ)

/-- The test vector in the fixed source compact picture. -/
def sourceAdjunctionCompactTest (hG : IsConnectedReductive G) (hK : IsCompact (K : Set Γ))
    (hψK : ∀ g : Γ, ∃ p : parabolic ψ, ∃ k : K, g = (p : Γ) * (k : Γ)) :
    CompactInductionPicture h₀ K A :=
  compactTestVector h₀ hU₀ hP₀ K hK hr₀ ν hν A
    (DynamicOppositeCanonicalScalar.radical_unimodular ψ hG) hψK
    t.isCompact_subgroup t.subgroup_le t.sourceFixed

/-- The test smooth functional section in the fixed target compact picture. -/
def targetAdjunctionCompactTest (hG : IsConnectedReductive G) (hK : IsCompact (K : Set Γ))
    (hψ'K : ∀ g : Γ, ∃ p : parabolic ψ', ∃ k : K, g = (p : Γ) * (k : Γ)) :
    CompactInductionPicture h₁ K A.contragredient :=
  compactTestVector h₁ hU₁ hP₁ K hK hr₁ ν hν A.contragredient
    (DynamicOppositeCanonicalScalar.radical_unimodular ψ' hG) hψ'K
    t.isCompact_subgroup t.subgroup_le t.targetFixed

local notation "s₀[" g "," k "," i "]" => sourceAdjunctionCompactTest χ K ψ hψ ψ' hψ' A t g k i
local notation "s₁[" g "," k "," i "]" => targetAdjunctionCompactTest χ K ψ hψ ψ' hψ' A t g k i
local notation "f[" z "]" => sourceAdjunctionTestSection χ K ψ hψ ψ' hψ' A t z
local notation "f'[" z "]" => targetAdjunctionTestSection χ K ψ hψ ψ' hψ' A t z
local notation "e₀[" g "," k "," i "," z "," B "]" => compactEquiv χ g K k ψ hψ i z B
local notation "e₁[" g "," k "," i "," z "," B "]" => compactEquiv χ g K k ψ' hψ' i z B
local notation "c[" k "]" => compactAdjunctionTestValue χ K k ψ hψ ψ' hψ' A t

/-- Restricting the source test section gives the same compact vector for every parameter. -/
theorem compactEquiv_sourceAdjunctionTestSection
    (hG : IsConnectedReductive G) (hK : IsCompact (K : Set Γ))
    (hψK : ∀ g : Γ, ∃ p : parabolic ψ, ∃ k : K, g = (p : Γ) * (k : Γ))
    (z : Z) :
    e₀[hG, hK, hψK, z, A] (f[z]) = s₀[hG, hK, hψK] :=
  unramifiedLeviInductionCompactEquiv_sourceTestVector h₀ hU₀ hP₀ K hK hr₀ ν hν A
    (DynamicOppositeCanonicalScalar.radical_unimodular ψ hG) hψK t.isCompact_subgroup t.subgroup_le t.sourceFixed (parameterTransport χ z)

/-- Restricting the target smooth-dual test also gives a fixed compact vector. -/
theorem compactEquiv_targetAdjunctionTestSection
    (hG : IsConnectedReductive G) (hK : IsCompact (K : Set Γ))
    (hψ'K : ∀ g : Γ, ∃ p : parabolic ψ', ∃ k : K, g = (p : Γ) * (k : Γ))
    (z : Z) :
    e₁[hG, hK, hψ'K, z⁻¹, A.contragredient] (f'[z]) = s₁[hG, hK, hψ'K] :=
  unramifiedLeviInductionCompactEquiv_sourceTestVector h₁ hU₁ hP₁ K hK hr₁ ν hν A.contragredient
    (DynamicOppositeCanonicalScalar.radical_unimodular ψ' hG) hψ'K t.isCompact_subgroup t.subgroup_le t.targetFixed (parameterTransport χ z⁻¹)

private theorem compactFamily_forwardTest_eq
    (hG : IsConnectedReductive G) (hK : IsCompact (K : Set Γ))
    (hψK : ∀ g : Γ, ∃ p : parabolic ψ, ∃ k : K, g = (p : Γ) * (k : Γ))
    (hψ'K : ∀ g : Γ, ∃ p : parabolic ψ', ∃ k : K, g = (p : Γ) * (k : Γ))
    (hδ : SquaredModulusCompatibility h₀ hU₀ h₁ hU₁)
    (z : pairFullDomainRegion χ K hK ψ hψ ψ' A) :
    compactPictureDualPairing h₁ K hK A
      (compactFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hδ A z s₀[hG, hK, hψK]) s₁[hG, hK, hψ'K] = c[hK] := by
  let J := pairFamily χ K hK ψ hψ ψ' hψ' hδ A z
  let j := J (f[z.val])
  have hsource := compactEquiv_sourceAdjunctionTestSection χ K ψ hψ ψ' hψ' A t hG hK hψK z.val
  have htarget := compactEquiv_targetAdjunctionTestSection χ K ψ hψ ψ' hψ' A t hG hK hψ'K z.val
  have hr : (e₀[hG, hK, hψK, z.val, A]).symm s₀[hG, hK, hψK] = f[z.val] :=
    (congrArg (e₀[hG, hK, hψK, z.val, A]).symm hsource.symm).trans
      ((e₀[hG, hK, hψK, z.val, A]).symm_apply_apply _)
  have hleft (k : K) : eval _ _ (compactFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hδ A z s₀[hG, hK, hψK]) k =
      eval (parabolic ψ') (leviInflatedInducingRepresentation h₁ hU₁ (twistObject χ z.val A)) j (k : Γ) :=
    (compactFamily_eval χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hδ A z s₀[hG, hK, hψK] k).trans
      (congrArg (fun w => eval _ _ (J w) (k : Γ)) hr)
  have hright (k : K) : eval _ _ s₁[hG, hK, hψ'K] k = eval (parabolic ψ')
      (leviInflatedInducingRepresentation h₁ hU₁ (twistObject χ z.val⁻¹ A.contragredient)) (f'[z.val]) (k : Γ) :=
    (congrArg (fun w : CompactInductionPicture h₁ K A.contragredient => eval _ _ w k) htarget.symm).trans
      (compactEquiv_eval χ hG K hK ψ' hψ' hψ'K z.val⁻¹ A.contragredient (f'[z.val]) k)
  exact (compactPictureDualPairing_eq_setIntegral h₁ K hK A _ _ _ _ hleft hright).trans
    (forward_testPairing_eq χ K hK ψ hψ ψ' hψ' A t z.val j hG hδ hψ'K
      (pairFamily_spec χ K hK ψ hψ ψ' hψ' hδ A z (f[z.val])))

private theorem compactFamily_reverseTest_eq
    (hG : IsConnectedReductive G) (hK : IsCompact (K : Set Γ))
    (hψK : ∀ g : Γ, ∃ p : parabolic ψ, ∃ k : K, g = (p : Γ) * (k : Γ))
    (hψ'K : ∀ g : Γ, ∃ p : parabolic ψ', ∃ k : K, g = (p : Γ) * (k : Γ))
    (hδ : SquaredModulusCompatibility h₀ hU₀ h₁ hU₁)
    (hδ' : SquaredModulusCompatibility h₁ hU₁ h₀ hU₀)
    (z : Z) (hz : z⁻¹ ∈ pairFullDomainRegion χ K hK ψ' hψ' ψ A.contragredient) :
    compactPictureDualPairing h₀ K hK A s₀[hG, hK, hψK]
      (compactFamily χ hG K hK ψ' hψ' hψ'K ψ hψ hψK hδ' A.contragredient ⟨z⁻¹, hz⟩ s₁[hG, hK, hψ'K]) = c[hK] := by
  let w : pairFullDomainRegion χ K hK ψ' hψ' ψ A.contragredient := ⟨z⁻¹, hz⟩
  let J := pairFamily χ K hK ψ' hψ' ψ hψ hδ' A.contragredient w
  let j := J (f'[z])
  have hsource := compactEquiv_sourceAdjunctionTestSection χ K ψ hψ ψ' hψ' A t hG hK hψK z
  have htarget := compactEquiv_targetAdjunctionTestSection χ K ψ hψ ψ' hψ' A t hG hK hψ'K z
  have hr : (e₁[hG, hK, hψ'K, z⁻¹, A.contragredient]).symm s₁[hG, hK, hψ'K] = f'[z] :=
    (congrArg (e₁[hG, hK, hψ'K, z⁻¹, A.contragredient]).symm htarget.symm).trans
      ((e₁[hG, hK, hψ'K, z⁻¹, A.contragredient]).symm_apply_apply _)
  have hleft (k : K) : eval _ _ s₀[hG, hK, hψK] k = eval (parabolic ψ)
      (leviInflatedInducingRepresentation h₀ hU₀ (twistObject χ z A)) (f[z]) (k : Γ) :=
    (congrArg (fun v : CompactInductionPicture h₀ K A => eval _ _ v k) hsource.symm).trans
      (compactEquiv_eval χ hG K hK ψ hψ hψK z A (f[z]) k)
  have hright (k : K) : eval _ _
      (compactFamily χ hG K hK ψ' hψ' hψ'K ψ hψ hψK hδ' A.contragredient w s₁[hG, hK, hψ'K]) k = eval (parabolic ψ)
      (leviInflatedInducingRepresentation h₀ hU₀ (twistObject χ z⁻¹ A.contragredient)) j (k : Γ) :=
    (compactFamily_eval χ hG K hK ψ' hψ' hψ'K ψ hψ hψK hδ' A.contragredient w s₁[hG, hK, hψ'K] k).trans
      (congrArg (fun v => eval _ _ (J v) (k : Γ)) hr)
  exact (compactPictureDualPairing_eq_setIntegral h₀ K hK A _ _ _ _ hleft hright).trans
    (reverse_testPairing_eq χ K hK ψ hψ ψ' hψ' A t z j hG hδ hψK hψ'K
      (pairFamily_spec χ K hK ψ' hψ' ψ hψ hδ' A.contragredient w (f'[z])))

/-- The original forward continuation has the exact nonzero compact test value
at every point of its displayed regular region. -/
theorem continuedPair_forwardTest_eq
    (hG : IsConnectedReductive G) (hK : IsCompact (K : Set Γ))
    (hψK : ∀ g : Γ, ∃ p : parabolic ψ, ∃ k : K, g = (p : Γ) * (k : Γ))
    (hψ'K : ∀ g : Γ, ∃ p : parabolic ψ', ∃ k : K, g = (p : Γ) * (k : Γ))
    (p : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A) (z : p.regularRegion) :
    compactPictureDualPairing h₁ K hK A (p.presentation.continuedOperator z s₀[hG, hK, hψK]) s₁[hG, hK, hψ'K] = c[hK] := by
  let E : CompactInductionPicture h₁ K A →ₗ[ℂ] ℂ := (compactPictureDualBilin h₁ K hK A).flip s₁[hG, hK, hψ'K]
  refine continuedOperator_map_eq_of_eqOn (parameterScheme χ)
    (DynamicOppositeCanonicalScalar.parameterProjection_continuous χ)
    (parameterScheme_isConnectedReductive χ hG) p.presentation p.isOpen_region p.nonempty_region
    (fun _ hz => hz) E s₀[hG, hK, hψK] c[hK] ?_ z
  intro x hx
  exact compactFamily_forwardTest_eq χ K ψ hψ ψ' hψ' A t hG hK hψK hψ'K p.modulus ⟨x, p.converges hx⟩

/-- The separately continued reverse-dual operator has the same compact test
value at every point of its displayed regular region. -/
theorem continuedPair_reverseTest_eq
    (hG : IsConnectedReductive G) (hK : IsCompact (K : Set Γ))
    (hψK : ∀ g : Γ, ∃ p : parabolic ψ, ∃ k : K, g = (p : Γ) * (k : Γ))
    (hψ'K : ∀ g : Γ, ∃ p : parabolic ψ', ∃ k : K, g = (p : Γ) * (k : Γ))
    (q : ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient)
    (hδ : SquaredModulusCompatibility h₀ hU₀ h₁ hU₁) (z : q.regularRegion) :
    compactPictureDualPairing h₀ K hK A s₀[hG, hK, hψK] (q.presentation.continuedOperator z s₁[hG, hK, hψ'K]) = c[hK] := by
  let E : CompactInductionPicture h₀ K A.contragredient →ₗ[ℂ] ℂ := compactPictureDualBilin h₀ K hK A s₀[hG, hK, hψK]
  refine continuedOperator_map_eq_of_eqOn (parameterScheme χ)
    (DynamicOppositeCanonicalScalar.parameterProjection_continuous χ)
    (parameterScheme_isConnectedReductive χ hG) q.presentation q.isOpen_region q.nonempty_region
    (fun _ hz => hz) E s₁[hG, hK, hψ'K] c[hK] ?_ z
  intro x hx
  change compactPictureDualPairing h₀ K hK A s₀[hG, hK, hψK]
    (compactFamily χ hG K hK ψ' hψ' hψ'K ψ hψ hψK q.modulus A.contragredient
      ⟨x, q.converges hx⟩ s₁[hG, hK, hψ'K]) = c[hK]
  have hx' : (x⁻¹)⁻¹ ∈ pairFullDomainRegion χ K hK ψ' hψ' ψ A.contragredient := by
    simpa only [inv_inv] using q.converges hx
  have he := compactFamily_reverseTest_eq χ K ψ hψ ψ' hψ' A t hG hK hψK hψ'K
    hδ q.modulus x⁻¹ hx'
  simpa only [inv_inv] using he

end Langlands.Plancherel.ActualCommonLeviIwasawa
