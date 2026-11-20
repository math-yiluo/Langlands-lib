import Langlands.Representation.Plancherel.ActualCommonLeviV3ScalarAlignment
import Langlands.Representation.Plancherel.ActualCommonLeviNonvanishing
import Langlands.Representation.Plancherel.ActualCommonLeviAmbientIrreducibility
import Langlands.Representation.Plancherel.ActualCommonLeviV3Continuation

/-! # Generic scalar inverse data from actual common-Levi continuations -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviV3

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviRationalTensor
open UnramifiedOperatorFamily

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
  ambientMeasurable ambientBorel leviLocallyCompact parabolicLocallyCompact

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

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

local notation "X" => unramifiedCharacters (normCharacters χ)
local notation "Freg" => unramifiedRegularFunctions (normCharacters χ)
local notation "h₀" => commonDecomposition χ ψ hψ
local notation "h₁" => commonDecomposition χ ψ' hψ'
local notation "hU₀" => radical_isClosed ψ
local notation "hU₁" => radical_isClosed ψ'
local notation "hδ₀" => DynamicOppositeCanonicalScalar.radical_unimodular ψ hG
local notation "hδ₁" => DynamicOppositeCanonicalScalar.radical_unimodular ψ' hG
local notation "hP₀" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ
local notation "hP₁" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ'
local notation "hr₀" => commonProjection_continuous χ ψ hψ
local notation "hr₁" => commonProjection_continuous χ ψ' hψ'
local notation "hp" => DynamicOppositeCanonicalScalar.parameterProjection_continuous χ
local notation "hL" => parameterScheme_isConnectedReductive χ hG
set_option quotPrecheck false in
local notation "I₀" z => (normalizedInductionFunctor h₀ hU₀).obj (twistObject χ z A)
set_option quotPrecheck false in
local notation "I₁" z => (normalizedInductionFunctor h₁ hU₁).obj (twistObject χ z A)

/-- Data for the first three clauses of the closed V.3.1 statement, with
the source and target normalized inductions irreducible on the genuine
locus of these chosen continuations. -/
structure GenericComparisonData where
  forward : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A
  reverse : ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient
  scalarInverse : ScalarInverseData χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A forward reverse
  hasDense : HasDenseGenericLocus χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K forward reverse
  irreducible : ∀ z : genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A forward reverse,
    (I₀ z.val).IsIrreducible ∧ (I₁ z.val).IsIrreducible

/-- The tensor on the genuine locus of these actual continuations is
rational with a whole-operator denominator. -/
theorem GenericComparisonData.rational
    (d : GenericComparisonData χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A) :
    IsRationalOperatorOn (genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A d.forward d.reverse)
      (compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A d.forward d.reverse) :=
  compactComparison_rational χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A d.forward d.reverse d.scalarInverse

variable
  (p : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)
  (q : ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient)
  (s : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A.contragredient)

set_option quotPrecheck false in
local notation "Js" => (fun z : s.region => pairFamily χ K hK ψ hψ ψ' hψ' s.modulus
  A.contragredient ⟨z.val, s.converges z.property⟩)
set_option quotPrecheck false in
local notation "Jq" => (fun z : q.region => pairFamily χ K hK ψ' hψ' ψ hψ q.modulus
  A.contragredient ⟨z.val, q.converges z.property⟩)

private theorem dualComposite_exists_scalar (x : ↥(s.regularRegion ∩ q.regularRegion))
    (hi : (UnramifiedLeviInduction h₀ hU₀ (leviNormCharacters χ)
      (parameterTransport χ x.val) A.contragredient).IsIrreducible) :
    ∃ c : ℂ, s.presentation.continuedComposite q.presentation x = c • LinearMap.id :=
  continuedInductionComposite_generic_scalar (parameterScheme χ) hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hψK hψ'K hr₀ hr₁ (parameterHomeomorph χ)
    (DynamicOppositeCanonicalScalar.normCharacters_continuous χ) A.contragredient Js Jq
    s.presentation q.presentation s.isOpen_region s.nonempty_region (fun _ hz => hz)
    q.isOpen_region q.nonempty_region (fun _ hz => hz) (D := {x.val})
    (fun _ hz => (Set.mem_singleton_iff.mp hz).symm ▸ hi) ⟨x.val, rfl, x.property⟩

private theorem scalarComposite_reverse
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (T : V →ₗ[ℂ] W) (S : W →ₗ[ℂ] V) (hT : Function.Surjective T)
    (c : ℂ) (h : S.comp T = c • LinearMap.id) : T.comp S = c • LinearMap.id := by
  ext w
  obtain ⟨v, hv⟩ := hT w
  change T (S w) = c • w
  rw [← hv]
  exact (congrArg T (LinearMap.congr_fun h v)).trans (T.map_smul c v)

private theorem exists_dual_composite_scalarFraction [Nontrivial A.contragredient] :
    ∃ a b : Freg, ∀ x : ↥(s.regularRegion ∩ q.regularRegion),
      b.val x.val ≠ 0 ∧
      ((UnramifiedLeviInduction h₀ hU₀ (leviNormCharacters χ)
        (parameterTransport χ x.val) A.contragredient).IsIrreducible →
          s.presentation.continuedComposite q.presentation x = (a.val x.val / b.val x.val) • LinearMap.id) := by
  obtain ⟨w, hw⟩ := exists_ne (0 : A.contragredient)
  let e := continuedPairCompactTest χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A.contragredient s w
  obtain ⟨c, hc, he⟩ := e.property
  have hne : e.val ≠ 0 := by
    obtain ⟨x, hx⟩ := s.nonempty_region
    intro h
    have hval := he ⟨x, s.presentation.subset_regularRegion hx⟩
    rw [h, map_zero, map_zero] at hval
    exact (smul_ne_zero hc hw) hval.symm
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one ℂ hne
  obtain ⟨a, b, _, hb, _, hval⟩ := continuedCompositeRationalScalar_spec (parameterScheme χ) hp hL
    s.presentation q.presentation s.nonempty_region q.nonempty_region e.val ℓ
  refine ⟨a, b, fun x => ⟨hb x, ?_⟩⟩
  intro hx
  obtain ⟨c', hc'⟩ := dualComposite_exists_scalar χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A q s x hx
  have hv : s.presentation.continuedCompositeScalar q.presentation e.val ℓ x = c' := by
    unfold RationalOperatorContinuationData.continuedCompositeScalar
    rw [hc', endomorphismScalarCoefficient_smul_id e.val ℓ hℓ]
  exact hc'.trans (congrArg (fun r : ℂ => r • LinearMap.id) (hv.symm.trans (hval x)))

variable
  (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)]
  (qMeasure : Measure (levi χ ⧸ C)) [qMeasure.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation qMeasure)
  (hi : A.representation.IsIrreducible) (hsplit : IsActualSplitCenter χ C)

/-- Supply the generic data of V.3.1 from the three actual continuations.
The forward presentation is refined so that both actual inductions are
irreducible throughout its genuine generic locus with the reverse dual. -/
def genericComparisonDataOfActualContinuations :
    GenericComparisonData χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A :=
  Classical.choice (by
    let i₀ := actualInductionIrreducibilityFactor χ A C hC qMeasure hG hsq hi hsplit ψ hψ
    let i₁ := actualInductionIrreducibilityFactor χ A C hC qMeasure hG hsq hi hsplit ψ' hψ'
    let iS := unramifiedRegularInversion (normCharacters χ) s.presentation.denominator
    let b : Freg := i₀.val * i₁.val * iS
    have hinv : iS ≠ 0 := by
      intro h
      exact (s.presentation.denominator_ne_zero s.nonempty_region)
        ((unramifiedRegularInversion (normCharacters χ)).injective
          (h.trans (map_zero (unramifiedRegularInversion (normCharacters χ))).symm))
    let := rationalUnramifiedRegularFunctions_isDomain (parameterScheme χ) hp hL
    have hb : b ≠ 0 := mul_ne_zero (mul_ne_zero i₀.property.1 i₁.property.1) hinv
    let O : Set X := regularLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q ∩ {z | b.val z ≠ 0}
    have hO (z : O) :
        (I₀ z.val).IsIrreducible ∧ (I₁ z.val).IsIrreducible ∧ z.val⁻¹ ∈ s.regularRegion := by
      have hz : (i₀.val.val z.val * i₁.val.val z.val) * s.presentation.denominator.val z.val⁻¹ ≠ 0 :=
        z.property.2
      have hzn := mul_ne_zero_iff.mp hz
      have hzi := mul_ne_zero_iff.mp hzn.1
      exact ⟨i₀.property.2 z.val hzi.1, i₁.property.2 z.val hzi.2, hzn.2⟩
    have hAz (z : X) : (twistObject χ z A).IsAdmissible :=
      (SmoothRep.isAdmissible_twist_iff (parameterTransport χ z).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z)) A).mpr hsq.1
    let : A.representation.IsIrreducible := hi
    let : Nontrivial A := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (levi χ)) A.representation.asModule
    let : A.contragredient.representation.IsIrreducible :=
      (SmoothRep.isIrreducible_contragredient_iff
        (compactOpenCofinal_of_nonarchimedean (levi χ)) A hsq.1).mpr hi
    let : Nontrivial A.contragredient :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (levi χ)) A.contragredient.representation.asModule
    have hdual₀ (z : O) := actualDualInduction_isIrreducible χ A hG ψ hψ K hK hψK z.val
      (hAz z.val) (hO z).1
    have hdual₁ (z : O) := actualDualInduction_isIrreducible χ A hG ψ' hψ' K hK hψ'K z.val
      (hAz z.val) (hO z).2.1
    let x (z : O) : ↥(s.regularRegion ∩ q.regularRegion) := ⟨z.val⁻¹, (hO z).2.2, z.property.1.2⟩
    let S (z : O) := s.presentation.continuedOperator ⟨z.val⁻¹, (hO z).2.2⟩
    let Q (z : O) := q.presentation.continuedOperator ⟨z.val⁻¹, z.property.1.2⟩
    have hP (z : O) :
        Function.Bijective (p.presentation.continuedOperator ⟨z.val, z.property.1.1⟩) :=
      (forward_bijective_iff_compact χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p
        ⟨z.val, z.property.1.1⟩).mp
        (continuedPair_operator_bijective_of_irreducible χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p
          ⟨z.val, z.property.1.1⟩
          ((Langlands.isIrreducible_iff_of_equiv
            (normalizedInductionLeviEquiv h₀ hU₀ hδ₀ (twistObject χ z.val A))).mp (hO z).1)
          ((Langlands.isIrreducible_iff_of_equiv
            (normalizedInductionLeviEquiv h₁ hU₁ hδ₁ (twistObject χ z.val A))).mp (hO z).2.1))
    have hS (z : O) : Function.Bijective (S z) :=
      (forward_bijective_iff_compact χ hG A.contragredient K hK ψ hψ hψK ψ' hψ' hψ'K s
        ⟨z.val⁻¹, (hO z).2.2⟩).mp
        (continuedPair_operator_bijective_of_irreducible χ hG K hK ψ hψ hψK ψ' hψ' hψ'K
          A.contragredient s ⟨z.val⁻¹, (hO z).2.2⟩ (hdual₀ z) (hdual₁ z))
    have hQ (z : O) : Function.Bijective (Q z) :=
      (forward_bijective_iff_compact χ hG A.contragredient K hK ψ' hψ' hψ'K ψ hψ hψK q
        ⟨z.val⁻¹, z.property.1.2⟩).mp
        (continuedPair_operator_bijective_of_irreducible χ hG K hK ψ' hψ' hψ'K ψ hψ hψK
          A.contragredient q ⟨z.val⁻¹, z.property.1.2⟩ (hdual₁ z) (hdual₀ z))
    obtain ⟨a, c, hfrac⟩ := exists_dual_composite_scalarFraction χ hG K hK ψ hψ hψK
      ψ' hψ' hψ'K A q s
    let a' := unramifiedRegularInversion (normCharacters χ) a
    let c' := unramifiedRegularInversion (normCharacters χ) c
    have hc' (z : O) : c'.val z.val ≠ 0 := (hfrac (x z)).1
    have hQS (z : O) : (Q z).comp (S z) = (a'.val z.val / c'.val z.val) • LinearMap.id :=
      (hfrac (x z)).2 (hdual₀ z)
    have ha' (z : O) : a'.val z.val ≠ 0 := by
      intro hz
      apply continuedPair_continuedOperator_ne_zero χ hG K hK ψ hψ hψK ψ' hψ' hψ'K
        A.contragredient s ⟨z.val⁻¹, (hO z).2.2⟩
      apply LinearMap.ext
      intro v
      change S z v = 0
      apply (hQ z).1
      have hv := LinearMap.congr_fun (hQS z) v
      change Q z (S z v) = (a'.val z.val / c'.val z.val) • v at hv
      rw [hz, zero_div, zero_smul] at hv
      exact hv.trans ((Q z).map_zero).symm
    let d := scalarInverseDataOfDenominatorFactor χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p b hb q
      s a' c' ha' hc' (fun z => (hO z).2.2) hP hQS
      (fun z => scalarComposite_reverse (S z) (Q z) (hS z).2 _ (hQS z))
    refine ⟨⟨continuedPairWithDenominatorFactor χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p b hb,
      q, d.val, d.property, ?_⟩⟩
    intro z
    have hz := (refinedRegularLocus_eq χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p b hb q).subset
      z.property.choose
    exact ⟨(hO ⟨z.val, hz⟩).1, (hO ⟨z.val, hz⟩).2.1⟩)

omit p q s in
/-- The owned closed common-Levi continuation theorem supplies every
continuation needed for the generic part of the stated V.3.1 task. -/
def genericComparisonDataOfContinuation
    (hcont : ConditionalDynamicCommonLeviContinuationStatement.{u, uV}) :
    GenericComparisonData χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A :=
  Classical.choice (by
    obtain ⟨⟨p₀⟩, _, ⟨s₀⟩, ⟨q₀⟩⟩ := nonempty_continuedPairs_of_continuation χ hG K hK
      ψ hψ hψK ψ' hψ' hψ'K A hcont hsq.1 hi
    exact ⟨genericComparisonDataOfActualContinuations χ hG K hK ψ hψ hψK
      ψ' hψ' hψ'K A p₀ q₀ s₀ C hC qMeasure hsq hi hsplit⟩)

end Langlands.Plancherel.ActualCommonLeviV3
