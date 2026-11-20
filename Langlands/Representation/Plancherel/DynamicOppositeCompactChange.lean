import Langlands.Representation.Plancherel.DynamicCommonLeviMeasureScaling
import Langlands.Representation.Plancherel.DynamicOppositeCanonicalScalar
import Langlands.Representation.Plancherel.TransportedCompactModelContinuation

/-! # Changing the source compact of the two actual opposite continuations -/

noncomputable section

set_option maxRecDepth 2048

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicOppositeCanonicalScalar

open Aubert.General Induction UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining DynamicCommonLeviComposition

attribute [local instance]
  dynamicOppositeCanonicalScalarIsAffine dynamicOppositeCanonicalScalarTopologicalSpace
  dynamicOppositeCanonicalScalarT2Space dynamicOppositeCanonicalScalarIsTopologicalGroup
  dynamicOppositeCanonicalScalarT2Space2 dynamicOppositeCanonicalScalarLocallyCompactSpace
  dynamicOppositeCanonicalScalarNonarchimedeanGroup
  dynamicOppositeCanonicalScalarSecondCountableTopology
  dynamicOppositeCanonicalScalarSecondCountableTopology2
  centralizerClosedImmersion centralizerAffine centralizerFiniteType
  dynamicOppositeCanonicalScalarTopologicalSpace2
  dynamicOppositeCanonicalScalarMeasurableSpace3 dynamicOppositeCanonicalScalarBorelSpace3
  dynamicOppositeCanonicalScalarMeasurableSpace4 dynamicOppositeCanonicalScalarBorelSpace4

private def rescaleContinuation {X : Type*} [Group X] [TopologicalSpace X]
    {I : Type*} {ν : I → (X →* ℝ≥0ˣ)}
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {Ω Λ : Set (unramifiedCharacters ν)}
    {J : Ω → V →ₗ[ℂ] W} {J' : Λ → V →ₗ[ℂ] W}
    (p : RationalOperatorContinuationData Ω J) (h : Λ ⊆ Ω) (c : ℂ)
    (he : ∀ z : Λ, J' z = c • J ⟨z.val, h z.property⟩) :
    RationalOperatorContinuationData Λ J' where
  denominator := p.denominator
  denominator_nonzero z := p.denominator_nonzero ⟨z.val, h z.property⟩
  numerator z := c • p.numerator z
  polynomial := by
    exact p.polynomial.regular_smul (algebraMap ℂ (unramifiedRegularFunctions ν) c)
  clears z := by
    rw [p.clears ⟨z.val, h z.property⟩, he z, smul_smul, smul_smul, mul_comm]

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (K L : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hL : IsCompact (L : Set (RationalPoint F G.X)))

local notation "χop" => Dynamic.inverseCocharacter χ
local notation "forwardScale" => pairQuotientHaarScale K L hK hL χ χop
local notation "reverseScale" => pairQuotientHaarScale K L hK hL χop χ
local notation "PF" => decomposition χ
local notation "PR" => oppositeDecomposition χ
local notation "UF" => radical_isClosed χ
local notation "UR" => oppositeRadical_isClosed χ

/-- The full domain of the forward integral is unchanged by the choice of source compact. -/
theorem forwardFullDomainRegion_changeCompact (A : SmoothRep.{0, u, uV} ℂ (levi χ)) :
    forwardFullDomainRegion χ L hL A = forwardFullDomainRegion χ K hK A :=
  pairFullDomainRegion_changeCompact K L hK hL χ χop χ rfl A

/-- The reverse full domain retains the original centralizer and character parameter. -/
theorem reverseFullDomainRegion_changeCompact (A : SmoothRep.{0, u, uV} ℂ (levi χ)) :
    reverseFullDomainRegion χ L hL A = reverseFullDomainRegion χ K hK A :=
  pairFullDomainRegion_changeCompact K L hK hL χop χ χ
    (Dynamic.centralizer_inverseCocharacter χ) A

variable
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

set_option maxHeartbeats 600000 in
private theorem forwardFamily_changeCompact (z : forwardFullDomainRegion χ L hL A)
    (hz : z.val ∈ forwardFullDomainRegion χ K hK A) :
    conditionalForwardFamily χ L hL hRefl hCST hG A z =
      (((forwardScale : ℝ≥0) : ℝ) : ℂ) •
        conditionalForwardFamily χ K hK hRefl hCST hG A ⟨z.val, hz⟩ := by
  refine DFunLike.ext _ _ fun f => ?_
  exact pairFamily_changeCompact K L hK hL χ χop χ rfl
    (Dynamic.centralizer_inverseCocharacter χ) A
    (conditionalSquaredModulus χ hRefl hCST hG) ⟨z.val, hz⟩ z.property f

set_option maxHeartbeats 600000 in
private theorem reverseFamily_changeCompact (z : reverseFullDomainRegion χ L hL A)
    (hz : z.val ∈ reverseFullDomainRegion χ K hK A) :
    conditionalReverseFamily χ L hL hRefl hCST hG A z =
      (((reverseScale : ℝ≥0) : ℝ) : ℂ) •
        conditionalReverseFamily χ K hK hRefl hCST hG A ⟨z.val, hz⟩ := by
  refine DFunLike.ext _ _ fun f => ?_
  exact pairFamily_changeCompact K L hK hL χop χ χ
    (Dynamic.centralizer_inverseCocharacter χ) rfl A
    (conditionalReverseSquaredModulus χ hRefl hCST hG) ⟨z.val, hz⟩ z.property f

variable
  (hPK : ∀ g : RationalPoint F G.X, ∃ p : parabolic χ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppK : ∀ g : RationalPoint F G.X, ∃ p : oppositeParabolic χ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hPL : ∀ g : RationalPoint F G.X, ∃ p : parabolic χ, ∃ l : L,
    g = (p : RationalPoint F G.X) * (l : RationalPoint F G.X))
  (hOppL : ∀ g : RationalPoint F G.X, ∃ p : oppositeParabolic χ, ∃ l : L,
    g = (p : RationalPoint F G.X) * (l : RationalPoint F G.X))

local notation "δF" => radical_unimodular χ hG
local notation "δR" => oppositeRadical_unimodular χ hG
local notation "closedF" => parabolic_isClosed χ
local notation "closedR" => oppositeParabolic_isClosed χ
local notation "projF" => projection_continuous χ
local notation "projR" => oppositeProjection_continuous χ
local notation "ΩF" => forwardFullDomainRegion χ K hK A
local notation "ΩR" => reverseFullDomainRegion χ K hK A
local notation "JF" => conditionalForwardFamily χ K hK hRefl hCST hG A
local notation "JR" => conditionalReverseFamily χ K hK hRefl hCST hG A
local notation "nChar" => normCharacters χ
local notation "hnChar" => normCharacters_continuous χ
local notation "e" => parameterHomeomorph χ

variable (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
  (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)

local notation "moveF" => transportedCompactModelContinuation PF UF δF PR UR δR K L
  closedF closedR hK hL hPK hPL hOppK hOppL e nChar hnChar projF projR A ΩF JF p
local notation "moveR" => transportedCompactModelContinuation PR UR δR PF UF δF K L
  closedR closedF hK hL hOppK hOppL hPK hPL e nChar hnChar projR projF A ΩR JR q

set_option maxHeartbeats 600000 in
/-- The forward continuation at the new Haar normalization. The actual
compact-model transport and the quotient measure scale preserve its denominator. -/
def forwardContinuationChangeCompact :
    ForwardContinuation χ hRefl hCST hG L hL hPL hOppL A :=
  rescaleContinuation moveF
    (forwardFullDomainRegion_changeCompact χ K L hK hL A).le
    (((forwardScale : ℝ≥0) : ℝ) : ℂ) (fun z => by
      unfold conditionalForwardCompactFamily
      rw [forwardFamily_changeCompact χ K L hK hL hRefl hCST hG A z
        ((forwardFullDomainRegion_changeCompact χ K L hK hL A).le z.property)]
      exact compactIntertwiningOperator_smul PF UF δF PR UR δR L hL closedF closedR
        hPL hOppL projF projR (leviNormCharacters χ)
        (fun ψ => (hnChar ψ).comp (e).symm.continuous) (parameterTransport χ z.val) A _ _)

set_option maxHeartbeats 600000 in
/-- The reverse continuation uses the reverse quotient measure scale and
the inverse direction of the same two compact models. -/
def reverseContinuationChangeCompact :
    ReverseContinuation χ hRefl hCST hG L hL hPL hOppL A :=
  rescaleContinuation moveR
    (reverseFullDomainRegion_changeCompact χ K L hK hL A).le
    (((reverseScale : ℝ≥0) : ℝ) : ℂ) (fun z => by
      unfold conditionalReverseCompactFamily
      rw [reverseFamily_changeCompact χ K L hK hL hRefl hCST hG A z
        ((reverseFullDomainRegion_changeCompact χ K L hK hL A).le z.property)]
      exact compactIntertwiningOperator_smul PR UR δR PF UF δF L hL closedR closedF
        hOppL hPL projR projF (leviNormCharacters χ)
        (fun ψ => (hnChar ψ).comp (e).symm.continuous) (parameterTransport χ z.val) A _ _)

local notation "pL" => forwardContinuationChangeCompact χ K L hK hL hRefl hCST hG A
  hPK hOppK hPL hOppL p
local notation "qL" => reverseContinuationChangeCompact χ K L hK hL hRefl hCST hG A
  hPK hOppK hPL hOppL q
set_option quotPrecheck false in
local notation "modelF" => unramifiedCompactModelEquiv PF UF δF K L closedF hK hL hPK hPL
  (leviNormCharacters χ) (fun ψ => (hnChar ψ).comp (e).symm.continuous) projF A
set_option quotPrecheck false in
local notation "modelR" => unramifiedCompactModelEquiv PR UR δR K L closedR hK hL hOppK hOppL
  (leviNormCharacters χ) (fun ψ => (hnChar ψ).comp (e).symm.continuous) projR A

set_option maxHeartbeats 600000 in
/-- The continued forward square commutes after including the exact Haar factor. -/
theorem forwardContinuationChangeCompact_apply (z : p.regularRegion)
    (f : CompactInductionPicture PF K A) :
    (pL).continuedOperator ⟨z.val, z.property⟩ (modelF (parameterTransport χ z.val) f) =
      (((forwardScale : ℝ≥0) : ℝ) : ℂ) •
        modelR (parameterTransport χ z.val) (p.continuedOperator z f) := by
  have hn := transportedCompactModelContinuation_continuedOperator_natural PF UF δF PR UR δR
    K L closedF closedR hK hL hPK hPL hOppK hOppL e nChar hnChar projF projR A ΩF JF p z f
  change (p.denominator.val z.val)⁻¹ •
      ((((forwardScale : ℝ≥0) : ℝ) : ℂ) •
        (moveF).numerator z.val (modelF (parameterTransport χ z.val) f)) = _
  rw [smul_comm]
  exact congrArg (fun x => (((forwardScale : ℝ≥0) : ℝ) : ℂ) • x) hn

set_option maxHeartbeats 600000 in
/-- The reverse square commutes on its original regular region with its
own Haar scalar. -/
theorem reverseContinuationChangeCompact_apply (z : q.regularRegion)
    (f : CompactInductionPicture PR K A) :
    (qL).continuedOperator ⟨z.val, z.property⟩ (modelR (parameterTransport χ z.val) f) =
      (((reverseScale : ℝ≥0) : ℝ) : ℂ) •
        modelF (parameterTransport χ z.val) (q.continuedOperator z f) := by
  have hn := transportedCompactModelContinuation_continuedOperator_natural PR UR δR PF UF δF
    K L closedR closedF hK hL hOppK hOppL hPK hPL e nChar hnChar projR projF A ΩR JR q z f
  change (q.denominator.val z.val)⁻¹ •
      ((((reverseScale : ℝ≥0) : ℝ) : ℂ) •
        (moveR).numerator z.val (modelR (parameterTransport χ z.val) f)) = _
  rw [smul_comm]
  exact congrArg (fun x => (((reverseScale : ℝ≥0) : ℝ) : ℂ) • x) hn

/-- The measure factor for the composite is the product for its two directed integrals. -/
def oppositeQuotientHaarScale : ℝ≥0 := forwardScale * reverseScale

theorem oppositeQuotientHaarScale_pos :
    0 < oppositeQuotientHaarScale χ K L hK hL :=
  mul_pos (pairQuotientHaarScale_pos K L hK hL χ χop)
    (pairQuotientHaarScale_pos K L hK hL χop χ)

local notation "scale" => (((oppositeQuotientHaarScale χ K L hK hL : ℝ≥0) : ℝ) : ℂ)

set_option maxHeartbeats 1000000 in
private theorem continuedComposite_changeCompact
    (z : ↥(p.regularRegion ∩ q.regularRegion)) (v : CompactInductionPicture PF K A) :
    (pL).continuedComposite qL ⟨z.val, z.property⟩ (modelF (parameterTransport χ z.val) v) =
      scale • modelF (parameterTransport χ z.val) (p.continuedComposite q z v) := by
  let zF : p.regularRegion := ⟨z.val, z.property.1⟩
  let zR : q.regularRegion := ⟨z.val, z.property.2⟩
  have hf := forwardContinuationChangeCompact_apply χ K L hK hL hRefl hCST hG A
    hPK hOppK hPL hOppL p zF v
  have hr := reverseContinuationChangeCompact_apply χ K L hK hL hRefl hCST hG A
    hPK hOppK hPL hOppL q zR (p.continuedOperator zF v)
  change (qL).continuedOperator ⟨zR.val, zR.property⟩
      ((pL).continuedOperator ⟨zF.val, zF.property⟩ (modelF (parameterTransport χ zF.val) v)) = _
  rw [hf, map_smul, hr]
  simp only [oppositeQuotientHaarScale, NNReal.coe_mul, Complex.ofReal_mul, smul_smul]
  rfl

set_option maxHeartbeats 1000000 in
private theorem continuedComposite_scalar_changeCompact
    (z : ↥(p.regularRegion ∩ q.regularRegion)) (v : CompactInductionPicture PF K A) (hv : v ≠ 0)
    (a b : ℂ) (ha : p.continuedComposite q z = a • LinearMap.id)
    (hb : (pL).continuedComposite qL ⟨z.val, z.property⟩ = b • LinearMap.id) :
    b = scale * a := by
  let E := modelF (parameterTransport χ z.val)
  have hEv : E v ≠ 0 := fun he => hv (E.injective (he.trans (map_zero E).symm))
  apply smul_left_injective ℂ hEv
  have hA := DFunLike.congr_fun ha v
  have hB := DFunLike.congr_fun hb (E v)
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at hA hB
  change b • E v = (scale * a) • E v
  calc
    _ = (pL).continuedComposite qL ⟨z.val, z.property⟩ (E v) := hB.symm
    _ = scale • E (p.continuedComposite q z v) :=
      continuedComposite_changeCompact χ K L hK hL hRefl hCST hG A
        hPK hOppK hPL hOppL p q z v
    _ = _ := by rw [hA, map_smul, smul_smul]

local notation "M" => parameterScheme χ
local notation "hp" => parameterProjection_continuous χ
local notation "hM" => parameterScheme_isConnectedReductive χ hG
local notation "Reg" => unramifiedRegularFunctions nChar
local notation "Frac" => rationalUnramifiedFunctionField M hp hM
local notation "ι" => algebraMap Reg Frac
set_option quotPrecheck false in
local notation "hLeviNorm" => (fun ψ => (hnChar ψ).comp (e).symm.continuous)

variable {DForward DReverse : Set (unramifiedCharacters (normCharacters χ))}
  (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
  (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
  (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
  (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
  {D : Set (unramifiedCharacters (normCharacters χ))} (hD : IsOpen D) (hne : D.Nonempty)
  (hi : ∀ z ∈ D, (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
    (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)

local notation "cK" => conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
  p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi

include hDForward hDReverse hD

set_option maxHeartbeats 600000 in
private theorem canonicalScalar_compact_spec :
    ∃ a b : Reg, b ≠ 0 ∧
      (∀ z : ↥(p.regularRegion ∩ q.regularRegion), b.val z.val ≠ 0) ∧
      cK = ι a / ι b ∧
      ∀ z : ↥(p.regularRegion ∩ q.regularRegion),
        p.continuedComposite q z = (a.val z.val / b.val z.val) • LinearMap.id := by
  obtain ⟨a, b, hb, hbR, hscalar, hspec⟩ := conditionalCanonicalRationalScalar_spec
    χ hRefl hCST hG K hK hPK hOppK A
    p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi
  refine ⟨a, b, hb, hbR, hscalar, fun z => ?_⟩
  exact (continuedInductionComposite_compact M hp hM
    PF UF δF PR UR δR K hK closedF closedR hPK hOppK projF projR e hnChar A JF JR
    p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ z).symm.trans
    ((compactIntertwiningOperator_scalar_iff PF UF δF K hK closedF hPK projF
      (leviNormCharacters χ) hLeviNorm (parameterTransport χ z.val) A
      _ _).mpr (hspec z))

local notation "hDForwardL" =>
  Set.Subset.trans hDForwardΩ (Eq.ge (forwardFullDomainRegion_changeCompact χ K L hK hL A))
local notation "hDReverseL" =>
  Set.Subset.trans hDReverseΩ (Eq.ge (reverseFullDomainRegion_changeCompact χ K L hK hL A))
local notation "cL" => conditionalCanonicalRationalScalar χ hRefl hCST hG L hL hPL hOppL A
  pL qL hneForward hDForwardL hneReverse hDReverseL hne hi

set_option maxHeartbeats 1000000 in
/-- With both compact pictures and both quotient Haar measures changed, the
canonical fraction scales by the positive product of the two measure factors. -/
theorem conditionalCanonicalRationalScalar_changeCompact :
    cL = ι (algebraMap ℂ Reg scale) * cK := by
  obtain ⟨aK, bK, hbK, hbKR, hcK, hKval⟩ := canonicalScalar_compact_spec
    χ K hK hRefl hCST hG A hPK hOppK p q
    hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi
  obtain ⟨aL, bL, hbL, hbLR, hcL, hLval⟩ := canonicalScalar_compact_spec
    χ L hL hRefl hCST hG A hPL hOppL pL qL
    hDForward hneForward hDForwardL hDReverse hneReverse hDReverseL hD hne hi
  obtain ⟨v, ℓ, hℓ⟩ := exists_normalized_compactCoefficient
    (χ := χ) (hG := hG) (K := K) (hK := hK) (hPK := hPK) (A := A) (hne := hne) (hi := hi)
  have hv : v ≠ 0 := by
    intro he
    rw [he, map_zero] at hℓ
    exact zero_ne_one hℓ
  have hvalue (z : ↥(p.regularRegion ∩ q.regularRegion)) :
      aL.val z.val / bL.val z.val = scale * (aK.val z.val / bK.val z.val) :=
    continuedComposite_scalar_changeCompact χ K L hK hL hRefl hCST hG A
      hPK hOppK hPL hOppL p q z v hv _ _ (hKval z) (hLval ⟨z.val, z.property⟩)
  let c : Reg := algebraMap ℂ Reg scale
  change cL = ι c * cK
  rw [hcL, hcK, ← mul_div_assoc, ← map_mul]
  have hcross : aL * bK = (c * aK) * bL := by
    apply sub_eq_zero.mp
    apply rationalUnramifiedRegular_eq_zero_of_isOpen M hp hM _
      (p.regularRegion_isOpen.inter q.regularRegion_isOpen)
      (continuedCompositeRegion_nonempty M hp hM p q
        (hneForward.mono hDForwardΩ) (hneReverse.mono hDReverseΩ))
    intro z hz
    change aL.val z * bK.val z - (scale * aK.val z) * bL.val z = 0
    apply sub_eq_zero.mpr
    apply (div_eq_div_iff (hbLR ⟨z, hz⟩) (hbKR ⟨z, hz⟩)).mp
    rw [mul_div_assoc]
    exact hvalue ⟨z, hz⟩
  have hinj := rationalUnramifiedFunctionField_algebraMap_injective M hp hM
  have hKne : ι bK ≠ 0 := fun h => hbK (hinj (h.trans (map_zero _).symm))
  have hLne : ι bL ≠ 0 := fun h => hbL (hinj (h.trans (map_zero _).symm))
  apply (div_eq_div_iff hLne hKne).mpr
  simpa only [map_mul] using congrArg (algebraMap Reg Frac) hcross

end Langlands.Plancherel.DynamicOppositeCanonicalScalar
