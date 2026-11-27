import Langlands.Representation.Plancherel.ActualCommonLeviV3UnitAdjunction
import Langlands.Representation.Plancherel.DynamicOppositeUnitaryNonnegativity
import Langlands.Representation.Unitary.Completion
import Langlands.Representation.Unitary.Twist

/-! # Fixed norms on the common-Levi compact pictures -/

noncomputable section

set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option quotPrecheck false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.ActualCommonLeviV3

open Aubert.General Induction CompactInduction
open DynamicOppositeStandardIntertwining DynamicCommonLeviComposition DynamicCommonLeviCompact
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviIwasawa

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
  DynamicCommonLeviContinuation.radicalMeasurable DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable DynamicCommonLeviContinuation.quotientBorel
  ambientMeasurable ambientBorel leviMeasurable leviBorel
  leviLocallyCompact parabolicLocallyCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : rationalPoints G, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : rationalPoints G) * (k : rationalPoints G))
  (b : InvariantPositiveForm A.representation)

set_option hygiene false in
local notation "d" => commonDecomposition χ ψ hψ
set_option hygiene false in
local notation "hU" => radical_isClosed ψ
set_option hygiene false in
local notation "hP" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ
set_option hygiene false in
local notation "hr" => commonProjection_continuous χ ψ hψ
set_option hygiene false in
local notation "hδ" => DynamicOppositeCanonicalScalar.radical_unimodular ψ hG
set_option hygiene false in
local notation "hPK" => iwasawa_sets K ψ hψK
set_option hygiene false in
local notation "hmod" => common_modularCharacter χ hG ψ hψ
set_option hygiene false in
local notation "Fibre" => CompactInductionPicture d K A
set_option hygiene false in
local notation "rest" => normalizedInductionCompactEquiv d K hU hP hK hψK

private theorem compactExtension_eval
    (B : SmoothRep.{0, u, uV} ℂ (levi χ)) (f : CompactInductionPicture d K B) (k : K) :
    eval (parabolic ψ) (inducingRepresentation d hU B) ((rest B).symm f) (k : rationalPoints G) =
      eval _ _ f k := by
  have h := normalizedInductionCompactEquiv_eval d K hU hP hK hψK B ((rest B).symm f) k
  rw [Representation.Equiv.apply_symm_apply] at h
  exact h.symm

/-- The fixed compact norm, transported from normalized induction with
compact Haar probability. -/
def compactNormModel : Fibre ≃ₗ[ℂ]
    (CompactInduction.invariantPositiveForm d hU hP K hK hPK
      (ambient_modularCharacter hG) hmod A b).NormedCarrier :=
  (rest A).symm.toLinearEquiv.trans
    (CompactInduction.invariantPositiveForm d hU hP K hK hPK
      (ambient_modularCharacter hG) hmod A b).toNormedCarrier

local notation "M" => compactNormModel χ hG A K hK ψ hψ hψK b

/-- In the fixed compact norm the inner product uses the given probability
integral on the compact group. -/
theorem compactNormModel_inner (f g : Fibre) :
    inner ℂ (M f) (M g) = compactPictureHermitianPairing d K hK A b f g := by
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  exact congrArg₂ b.inner
    (compactExtension_eval χ K hK ψ hψ hψK A f k)
    (compactExtension_eval χ K hK ψ hψ hψK A g k)

/-- At every unitary parameter the actual norm on normalized induction
pulls back to the same compact norm. -/
theorem compactNormModel_twist_inner
    (z : unitaryUnramifiedCharacters (normCharacters χ))
    (f g : UnramifiedLeviInduction d hU (leviNormCharacters χ)
      (parameterTransport χ (unitaryParameter χ z)) A) :
    let w := unitaryParameter χ z
    let B := twistObject χ w A
    let bt := b.twist (parameterTransport χ w).val.toMonoidHom (unitary_parameter_norm χ z)
    let e := (normalizedInductionLeviEquiv d hU hδ B).symm
    let C := compactEquiv χ hG K hK ψ hψ hψK w A
    inner ℂ (M (C f)) (M (C g)) =
      (CompactInduction.invariantPositiveForm d hU hP K hK hPK
        (ambient_modularCharacter hG) hmod B bt).inner (e f) (e g) := by
  dsimp only
  rw [compactNormModel_inner, CompactInduction.invariantPositiveForm_inner]
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  exact congrArg₂ b.inner
    ((compactEquiv_eval χ hG K hK ψ hψ hψK _ A f k).trans
      (normalizedInductionLeviEquiv_symm_eval d hU hδ (twistObject χ _ A) f k).symm)
    ((compactEquiv_eval χ hG K hK ψ hψ hψK _ A g k).trans
      (normalizedInductionLeviEquiv_symm_eval d hU hδ (twistObject χ _ A) g k).symm)

include hG in
/-- Each fixed compact dual vector defines a bounded functional for the
compact Haar norm through normalized induction's integral duality. -/
theorem exists_compactPictureDualPairing_norm_bound (hadm : A.IsAdmissible)
    (ℓ : CompactInductionPicture d K A.contragredient) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Fibre,
      ‖compactPictureDualPairing d K hK A f ℓ‖ ≤ C * ‖M f‖ := by
  let I := (normalizedInductionFunctor d hU).obj A
  let B := CompactInduction.invariantPositiveForm d hU hP K hK hPK (ambient_modularCharacter hG) hmod A b
  let S := integralDualEquiv d hU hP hr K hK hPK (ambient_modularCharacter hG) hmod A hadm
  let ℓ' : I.contragredient := S.symm ((rest A.contragredient).symm ℓ)
  have hI : I.IsAdmissible := induced_isAdmissible d hU K hK hPK A hr hadm
  let e := B.smoothDualEquiv (compactOpenCofinal_of_nonarchimedean (rationalPoints G)) hI
  obtain ⟨v, hv⟩ := e.surjective ℓ'
  refine ⟨‖B.toNormedCarrier v‖, norm_nonneg _, fun f => ?_⟩
  let g := (rest A).symm f
  have he : smoothDualPairing I.representation ℓ' g = compactPictureDualPairing d K hK A f ℓ := by
    refine (integralDualEquiv_pairing d hU hP hr K hK hPK (ambient_modularCharacter hG)
      hmod A hadm ℓ' g).trans (integral_congr_ae (ae_of_all _ fun k => ?_))
    have hs : S ℓ' = (rest A.contragredient).symm ℓ := S.apply_symm_apply _
    have hℓ : eval (parabolic ψ) (inducingRepresentation d hU A.contragredient)
        (S ℓ') (k : rationalPoints G) = eval _ _ ℓ k :=
      (congrArg (fun v => eval (parabolic ψ) (inducingRepresentation d hU A.contragredient)
        v (k : rationalPoints G)) hs).trans (compactExtension_eval χ K hK ψ hψ hψK A.contragredient ℓ k)
    exact congrArg₂ (fun (x : A.contragredient) (y : A) => smoothDualPairing A.representation x y)
      hℓ (compactExtension_eval χ K hK ψ hψ hψK A f k)
  rw [← he, ← hv]
  exact norm_inner_le_norm (𝕜 := ℂ) (B.toNormedCarrier v) (B.toNormedCarrier g)

variable (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : rationalPoints G, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : rationalPoints G) * (k : rationalPoints G))
  (p : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)
  (q : ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient)

set_option hygiene false in
local notation "d'" => commonDecomposition χ ψ' hψ'
set_option hygiene false in
local notation "hU'" => radical_isClosed ψ'
set_option hygiene false in
local notation "hP'" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ'
set_option hygiene false in
local notation "hδ'" => DynamicOppositeCanonicalScalar.radical_unimodular ψ' hG
set_option hygiene false in
local notation "Fibre'" => CompactInductionPicture d' K A
set_option hygiene false in
local notation "M'" => compactNormModel χ hG A K hK ψ' hψ' hψ'K b
set_option hygiene false in
local notation "D" => genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
set_option hygiene false in
local notation "Xu" => unitaryUnramifiedCharacters (normCharacters χ)

set_option maxHeartbeats 2400000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- On an irreducible unitary source the forward operator is a positive
similitude for the two fixed, compact probability norms. -/
theorem exists_compactForward_similitude
    (hadm : A.IsAdmissible) (z : Xu) (hz : unitaryParameter χ z ∈ D)
    (hirr : ((normalizedInductionFunctor d hU).obj (twistObject χ (unitaryParameter χ z) A)).IsIrreducible) :
    ∃ r : ℝ, 0 < r ∧ ∀ v : Fibre,
      ‖M' (p.presentation.continuedOperator ⟨unitaryParameter χ z, hz.choose.1⟩ v)‖ =
        r * ‖M v‖ := by
  let w := unitaryParameter χ z
  let x : D := ⟨w, hz⟩
  let B := twistObject χ w A
  let c := parameterTransport χ w
  let bt := b.twist c.val.toMonoidHom (unitary_parameter_norm χ z)
  have hB : B.IsAdmissible := (SmoothRep.isAdmissible_twist_iff c.val.toMonoidHom
    (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) c) A).mpr hadm
  let e := genericNormalizedForwardEquiv χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q x
  let s := genericForwardSimilitude χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q x hB hirr bt
  let B₀ := CompactInduction.invariantPositiveForm d hU hP K hK hPK
    (ambient_modularCharacter hG) hmod B bt
  let B₁ := CompactInduction.invariantPositiveForm d' hU' hP' K hK (iwasawa_sets K ψ' hψ'K)
    (ambient_modularCharacter hG) (common_modularCharacter χ hG ψ' hψ') B bt
  have hform : B₁.ofEquiv e = B₀.rescale s.val s.property.choose := s.property.choose_spec
  refine ⟨Real.sqrt s.val, Real.sqrt_pos.2 s.property.choose, fun v => ?_⟩
  let a₀ := normalizedInductionLeviEquiv d hU hδ B
  let a₁ := normalizedInductionLeviEquiv d' hU' hδ' B
  let C₀ := compactEquiv χ hG K hK ψ hψ hψK w A
  let C₁ := compactEquiv χ hG K hK ψ' hψ' hψ'K w A
  let f := C₀.symm v
  let f₀ := a₀.symm f
  let u : p.regularRegion := ⟨w, hz.choose.1⟩
  let J := ContinuedPair.operator χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p u
  let g := J f
  have hf : C₀ f = v := C₀.apply_symm_apply v
  have he : e f₀ = a₁.symm g := by
    change a₁.symm (J (a₀ (a₀.symm f))) = _
    rw [a₀.apply_symm_apply]
  have hJ : C₁ g = p.presentation.continuedOperator u v :=
    (forward_compact_square χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p u f).trans
      (congrArg (p.presentation.continuedOperator u) hf)
  have h₀ : inner ℂ (M v) (M v) = B₀.inner f₀ f₀ := by
    rw [← hf]
    exact compactNormModel_twist_inner χ hG A K hK ψ hψ hψK b z f f
  have h₁ : inner ℂ (M' (p.presentation.continuedOperator u v))
      (M' (p.presentation.continuedOperator u v)) = B₁.inner (e f₀) (e f₀) := by
    rw [← hJ, he]
    exact compactNormModel_twist_inner χ hG A K hK ψ' hψ' hψ'K b z g g
  have hs : B₁.inner (e f₀) (e f₀) = (s.val : ℂ) * B₀.inner f₀ f₀ :=
    congrArg (fun H => H.inner f₀ f₀) hform
  change ‖M' (p.presentation.continuedOperator u v)‖ = Real.sqrt s.val * ‖M v‖
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), h₁, hs, ← h₀]
  change Real.sqrt (((s.val : ℂ) * inner ℂ (M v) (M v)).re) = Real.sqrt s.val * ‖M v‖
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Real.sqrt_mul s.property.choose.le]
  rfl

include hG in
set_option maxHeartbeats 1600000 in
/-- The inverse of the forward continued intertwiner is uniformly bounded in
the fixed compact norms at its generic irreducible unitary parameters. -/
theorem exists_uniform_compactForward_inverse_bound [Nontrivial A] (hadm : A.IsAdmissible) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Xu) (hz : unitaryParameter χ z ∈ D),
      ((normalizedInductionFunctor d hU).obj (twistObject χ (unitaryParameter χ z) A)).IsIrreducible →
      ∀ v : Fibre,
        ‖M v‖ ≤ C * ‖M' (p.presentation.continuedOperator ⟨unitaryParameter χ z, hz.choose.1⟩ v)‖ := by
  let t := chooseCompactAdjunctionTest χ K ψ hψ ψ' hψ' A hG
  let f := sourceAdjunctionCompactTest χ K ψ hψ ψ' hψ' A t hG hK hψK
  let ℓ := targetAdjunctionCompactTest χ K ψ hψ ψ' hψ' A t hG hK hψ'K
  let a := compactAdjunctionTestValue χ K hK ψ hψ ψ' hψ' A t
  have ha : 0 < ‖a‖ := norm_pos_iff.mpr (compactAdjunctionTestValue_ne_zero χ K hK ψ hψ ψ' hψ' A t)
  obtain ⟨T, hT, hTest⟩ := exists_compactPictureDualPairing_norm_bound χ hG A K hK ψ' hψ' hψ'K b hadm ℓ
  let C := T * ‖M f‖ / ‖a‖
  refine ⟨C, div_nonneg (mul_nonneg hT (norm_nonneg _)) ha.le, fun z hz hirr v => ?_⟩
  let u : p.regularRegion := ⟨unitaryParameter χ z, hz.choose.1⟩
  let J := p.presentation.continuedOperator u
  obtain ⟨r, _, hs⟩ := exists_compactForward_similitude χ hG A K hK ψ hψ hψK b
    ψ' hψ' hψ'K p q hadm z hz hirr
  have he := continuedPair_forwardTest_eq χ K ψ hψ ψ' hψ' A t hG hK hψK hψ'K p u
  have hlow : ‖a‖ ≤ T * (r * ‖M f‖) := by
    have h := hTest (J f)
    change ‖compactPictureDualPairing d' K hK A (J f) ℓ‖ ≤ T * ‖M' (J f)‖ at h
    have ht : compactPictureDualPairing d' K hK A (J f) ℓ = a := he
    rwa [ht, hs f] at h
  have hmul : 1 ≤ C * r := by
    dsimp only [C]
    rw [div_mul_eq_mul_div, le_div_iff₀ ha, one_mul]
    simpa only [mul_assoc, mul_comm r] using hlow
  change ‖M v‖ ≤ C * ‖M' (J v)‖
  calc
    ‖M v‖ = 1 * ‖M v‖ := (one_mul _).symm
    _ ≤ (C * r) * ‖M v‖ := mul_le_mul_of_nonneg_right hmul (norm_nonneg _)
    _ = C * ‖M' (J v)‖ := by rw [hs v, mul_assoc]

end Langlands.Plancherel.ActualCommonLeviV3
