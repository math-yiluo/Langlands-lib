import Langlands.Representation.Plancherel.DynamicOppositeCompactChange
import Langlands.Representation.Plancherel.DynamicCommonLeviContinuation
import Langlands.Representation.Plancherel.DynamicOppositePairScalarProof
import Langlands.Representation.Plancherel.ActualCommonLeviTensor

/-! # The canonical opposite scalar on actual compact continuations -/

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

open ActualCommonLeviTensor DynamicCommonLeviCompact DynamicCommonLeviContinuation

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))

local notation "χop" => Dynamic.inverseCocharacter χ
local notation "PF" => decomposition χ
local notation "PR" => oppositeDecomposition χ
local notation "UF" => radical_isClosed χ
local notation "UR" => oppositeRadical_isClosed χ

variable
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

variable
  (hPK : ∀ g : RationalPoint F G.X, ∃ p : parabolic χ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppK : ∀ g : RationalPoint F G.X, ∃ p : oppositeParabolic χ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

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
/-- The compact form of the opposite-composite scalar identity. The two
compact continuations retain the actual quotient measures of their source families. -/
theorem conditionalCanonicalRationalScalar_compact_spec :
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

attribute [local instance]
  DynamicCommonLeviContinuation.radicalMeasurable DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable DynamicCommonLeviContinuation.quotientBorel

local notation "he" => Dynamic.centralizer_inverseCocharacter χ

omit hDForward hDReverse hD in
/-- A continuation chosen on an open convergence region of the same
ordered pair agrees with the specified forward continuation. -/
theorem oppositeForwardContinuedPair_eq
    (p₀ : ContinuedPair χ hG K hK χ rfl hPK χop he hOppK A)
    (z : ↥(p₀.regularRegion ∩ p.regularRegion)) :
    p₀.presentation.continuedOperator ⟨z.val, z.property.1⟩ =
      p.continuedOperator ⟨z.val, z.property.2⟩ := by
  have h := rationalOperatorContinuationData_natural M hp hM p₀.presentation p
    LinearMap.id LinearMap.id p₀.isOpen_region p₀.nonempty_region subset_rfl
    (fun _ hx => p₀.converges hx) (fun _ _ => by
      rw [LinearMap.comp_id, LinearMap.id_comp]
      rfl) z
  simpa only [LinearMap.comp_id, LinearMap.id_comp] using h.symm

omit hDForward hDReverse hD in
/-- A continuation chosen on an open convergence region of the reverse
ordered pair agrees with the specified reverse continuation. -/
theorem oppositeReverseContinuedPair_eq
    (q₀ : ContinuedPair χ hG K hK χop he hOppK χ rfl hPK A)
    (z : ↥(q₀.regularRegion ∩ q.regularRegion)) :
    q₀.presentation.continuedOperator ⟨z.val, z.property.1⟩ =
      q.continuedOperator ⟨z.val, z.property.2⟩ := by
  have h := rationalOperatorContinuationData_natural M hp hM q₀.presentation q
    LinearMap.id LinearMap.id q₀.isOpen_region q₀.nonempty_region subset_rfl
    (fun _ hx => q₀.converges hx) (fun _ _ => by
      rw [LinearMap.comp_id, LinearMap.id_comp]
      rfl) z
  simpa only [LinearMap.comp_id, LinearMap.id_comp] using h.symm

end Langlands.Plancherel.DynamicOppositeCanonicalScalar
