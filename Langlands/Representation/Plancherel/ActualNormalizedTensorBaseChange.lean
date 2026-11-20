import Langlands.Representation.Plancherel.ActualCommonLeviCompactTensor
import Langlands.Representation.Plancherel.ActualCommonLeviBaseChange

/-! # The genuine continued normalized tensor under a change of orbit base -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types true

universe u uV uW

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualNormalizedTensorBaseChange

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor UnramifiedOperatorFamily

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
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicCommonLeviContinuation.radicalMeasurable
  DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable
  DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable
  DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  {A : SmoothRep.{0, u, uV} ℂ (levi χ)} {B : SmoothRep.{0, u, uW} ℂ (levi χ)}

set_option hygiene false in
local notation "X" => unramifiedCharacters (normCharacters χ)
set_option hygiene false in
local notation "h₀" => commonDecomposition χ ψ hψ
set_option hygiene false in
local notation "h₁" => commonDecomposition χ ψ' hψ'
set_option hygiene false in
local notation "hU₀" => radical_isClosed ψ
set_option hygiene false in
local notation "hU₁" => radical_isClosed ψ'
set_option hygiene false in
local notation "hδ₀" => DynamicOppositeCanonicalScalar.radical_unimodular ψ hG
set_option hygiene false in
local notation "hδ₁" => DynamicOppositeCanonicalScalar.radical_unimodular ψ' hG
set_option hygiene false in
local notation "hP₀" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ
set_option hygiene false in
local notation "hP₁" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ'
set_option hygiene false in
local notation "hr₀" => commonProjection_continuous χ ψ hψ
set_option hygiene false in
local notation "hr₁" => commonProjection_continuous χ ψ' hψ'
set_option hygiene false in
local notation "hν" => DynamicOppositeCanonicalScalar.normCharacters_continuous χ

variable (τ : X) (a : (twistObject χ τ A).representation.Equiv B.representation)

/-- The actual compact coordinate change induced by the equivalence from the
shifted orbit base to the new inducing object. It is independent of `z`. -/
def compactBaseEquiv :
    (CompactInductionPicture h₀ K A) ≃ₗ[ℂ] (CompactInductionPicture h₀ K B) :=
  (compactInductionBaseChangeEquiv h₀ K hP₀ hK (leviNormCharacters χ)
    (fun i => (hν i).comp (parameterHomeomorph χ).symm.continuous)
    hr₀ (parameterTransport χ τ) a).toLinearEquiv

section Continuations

variable
  (pA : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)
  (pB : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K B)

set_option hygiene false in
local notation "C₀" => compactBaseEquiv χ K hK ψ hψ τ a
set_option hygiene false in
local notation "C₁" => compactBaseEquiv χ K hK ψ' hψ' τ a
set_option hygiene false in
local notation "D" => (unramifiedParameterTranslation (normCharacters χ) τ) ⁻¹' pA.region ∩ pB.region

/-- The actual original integral square propagates to any common regular
value of these independent continuations. The starting overlap is explicit. -/
theorem continuedCompactSquare (hne : (D).Nonempty) (z : X)
    (hzA : τ * z ∈ pA.regularRegion) (hzB : z ∈ pB.regularRegion) :
    (pB.presentation.continuedOperator ⟨z, hzB⟩).comp (C₀).toLinearMap =
      (C₁).toLinearMap.comp (pA.presentation.continuedOperator ⟨τ * z, hzA⟩) := by
  have hD : IsOpen D := (pA.isOpen_region.preimage
    (unramifiedParameterTranslation (normCharacters χ) τ).continuous).inter pB.isOpen_region
  refine rationalOperatorContinuationData_translation_natural (parameterScheme χ)
    (DynamicOppositeCanonicalScalar.parameterProjection_continuous χ)
    (parameterScheme_isConnectedReductive χ hG) τ pA.presentation pB.presentation
    (C₀).toLinearMap (C₁).toLinearMap hD hne (fun _ h => h.1) (fun _ h => h.2)
    (fun w hw => ?_) ⟨z, hzA, hzB⟩
  apply LinearMap.ext
  intro v
  have h := (compactIntertwiningOperator_transportedBaseChange_iff (parameterHomeomorph χ)
    (normCharacters χ) h₀ hU₀ hδ₀ K hP₀ hK hψK hν hr₀
    h₁ hU₁ hδ₁ hP₁ hψ'K hr₁ τ w a
    (pairFamily χ K hK ψ hψ ψ' hψ' pA.modulus A ⟨τ * w, pA.converges hw.1⟩)
    (pairFamily χ K hK ψ hψ ψ' hψ' pB.modulus B ⟨w, pB.converges hw.2⟩)).mp
    (fun f => ActualCommonLeviBaseChange.originalSquare χ K hK ψ hψ ψ' hψ'
      pA.modulus τ w a (pB.converges hw.2) f) v
  exact h

end Continuations

/-- On the actual inducing smooth duals, base change uses the inverse twist
and inverse pullback of the given inducing equivalence. -/
def dualBaseEquiv :
    (twistObject χ τ⁻¹ A.contragredient).representation.Equiv B.contragredient.representation :=
  (dualTwistEquiv χ τ A).symm.trans (smoothContragredientEquiv a.symm)

/-- The fixed compact coefficient tensor comparison with both canonical
inducing-factor equivalences. -/
def compactTensorBaseEquiv : compactFiber χ K ψ hψ A ≃ₗ[ℂ] compactFiber χ K ψ hψ B :=
  TensorProduct.congr (compactBaseEquiv χ K hK ψ hψ τ a)
    (compactBaseEquiv χ K hK ψ hψ τ⁻¹ (dualBaseEquiv χ τ a))


/-- Read the fixed inducing coordinate change on the actual source-normalized
coefficient fibers at corresponding parameters. -/
def coefficientBaseEquiv (z : X) :
    coefficientFiber χ ψ hψ A (τ * z) ≃ₗ[ℂ] coefficientFiber χ ψ hψ B z :=
  (compactTensorEquiv χ hG K hK ψ hψ hψK A (τ * z)).trans
    ((compactTensorBaseEquiv χ K hK ψ hψ τ a).trans
      (compactTensorEquiv χ hG K hK ψ hψ hψK B z).symm)

/-- The ambient and compact changes of the orbit base are compatible. -/
theorem coefficientBaseEquiv_compact (z : X) (v : coefficientFiber χ ψ hψ A (τ * z)) :
    compactTensorEquiv χ hG K hK ψ hψ hψK B z
        (coefficientBaseEquiv χ hG K hK ψ hψ hψK τ a z v) =
      compactTensorBaseEquiv χ K hK ψ hψ τ a
        (compactTensorEquiv χ hG K hK ψ hψ hψK A (τ * z) v) := by
  simp only [coefficientBaseEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

section TensorSquare

variable
  (pA : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)
  (qA : ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient)
  (pB : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K B)
  (qB : ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK B.contragredient)
  (z : X)
  (hA : τ * z ∈ genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A pA qA)
  (hB : z ∈ genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K B pB qB)

set_option hygiene false in
local notation "zA" => (⟨τ * z, hA⟩ : genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A pA qA)
set_option hygiene false in
local notation "zB" => (⟨z, hB⟩ : genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K B pB qB)
set_option hygiene false in
local notation "C₀" => compactBaseEquiv χ K hK ψ hψ τ a
set_option hygiene false in
local notation "C₁" => compactBaseEquiv χ K hK ψ' hψ' τ a
set_option hygiene false in
local notation "D₀" => compactBaseEquiv χ K hK ψ hψ τ⁻¹ (dualBaseEquiv χ τ a)
set_option hygiene false in
local notation "D₁" => compactBaseEquiv χ K hK ψ' hψ' τ⁻¹ (dualBaseEquiv χ τ a)
set_option hygiene false in
local notation "IA" => compactReverseInverse χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A pA qA zA
set_option hygiene false in
local notation "IB" => compactReverseInverse χ hG K hK ψ hψ hψK ψ' hψ' hψ'K B pB qB zB
set_option hygiene false in
set_option quotPrecheck false in
local notation "RA" => qA.presentation.continuedOperator ⟨(τ * z)⁻¹, hA.choose.2⟩
set_option hygiene false in
set_option quotPrecheck false in
local notation "RB" => qB.presentation.continuedOperator ⟨z⁻¹, hB.choose.2⟩

variable
  (hForward : ((unramifiedParameterTranslation (normCharacters χ) τ) ⁻¹' pA.region ∩ pB.region).Nonempty)
  (hReverse : ((unramifiedParameterTranslation (normCharacters χ) τ⁻¹) ⁻¹' qA.region ∩ qB.region).Nonempty)

include hReverse in
/-- The square for the actual reverse continuation gives the inverse square
at the inverse parameter, on the simultaneous genuine generic locus. -/
theorem reverseInverseSquare (ℓ : CompactInductionPicture h₀ K A.contragredient) :
    IB (D₀ ℓ) = D₁ (IA ℓ) := by
  have hp : τ⁻¹ * z⁻¹ ∈ qA.regularRegion := by
    rw [← mul_inv]
    exact hA.choose.2
  have heq : (⟨τ⁻¹ * z⁻¹, hp⟩ : qA.regularRegion) = ⟨(τ * z)⁻¹, hA.choose.2⟩ :=
    Subtype.ext (mul_inv τ z).symm
  have hs := continuedCompactSquare χ hG K hK ψ' hψ' hψ'K ψ hψ hψK
    τ⁻¹ (dualBaseEquiv χ τ a) qA qB hReverse z⁻¹ hp hB.choose.2
  rw [heq] at hs
  apply (compactReverse_bijective χ hG K hK ψ hψ hψK ψ' hψ' hψ'K B pB qB zB).injective
  calc
    RB (IB (D₀ ℓ)) = D₀ ℓ :=
      compactReverseInverse_right χ hG K hK ψ hψ hψK ψ' hψ' hψ'K B pB qB zB (D₀ ℓ)
    _ = D₀ (RA (IA ℓ)) :=
      (congrArg D₀ (compactReverseInverse_right χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A pA qA zA ℓ)).symm
    _ = RB (D₁ (IA ℓ)) := (congrArg (fun T => T (IA ℓ)) hs).symm

include hForward hReverse in
/-- This particular normalized tensor commutes with fixed base transport
on the joint generic locus of the two independently continued pairs. -/
theorem compactTensorSquare :
    (compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K B pB qB zB).comp
        (compactTensorBaseEquiv χ K hK ψ hψ τ a).toLinearMap =
      (compactTensorBaseEquiv χ K hK ψ' hψ' τ a).toLinearMap.comp
        (compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A pA qA zA) := by
  apply TensorProduct.ext'
  intro f ℓ
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, compactTensorBaseEquiv,
    compactComparison, TensorProduct.congr_tmul, TensorProduct.map_tmul]
  refine congrArg₂ (TensorProduct.tmul ℂ) ?_ ?_
  · exact congrArg (fun T => T f)
      (continuedCompactSquare χ hG K hK ψ hψ hψK ψ' hψ' hψ'K
        τ a pA pB hForward z hA.choose.1 hB.choose.1)
  · exact reverseInverseSquare χ hG K hK ψ hψ hψK ψ' hψ' hψ'K
      τ a pA qA pB qB z hA hB hReverse ℓ

set_option maxHeartbeats 2400000 in
set_option backward.isDefEq.respectTransparency.types false in
include hForward hReverse in
/-- The same square holds on every vector of the actual ambient coefficient
fibers, using the published compact realization of the two tensors. -/
theorem coefficientTensorSquare (v : coefficientFiber χ ψ hψ A (τ * z)) :
    genericComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K B pB qB zB
        (coefficientBaseEquiv χ hG K hK ψ hψ hψK τ a z v) =
      coefficientBaseEquiv χ hG K hK ψ' hψ' hψ'K τ a z
        (genericComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A pA qA zA v) := by
  apply (compactTensorEquiv χ hG K hK ψ' hψ' hψ'K B z).injective
  have hAJ := compactComparison_square χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A pA qA zA v
  have hBJ := compactComparison_square χ hG K hK ψ hψ hψK ψ' hψ' hψ'K B pB qB zB
    (coefficientBaseEquiv χ hG K hK ψ hψ hψK τ a z v)
  have hSource := coefficientBaseEquiv_compact χ hG K hK ψ hψ hψK τ a z v
  have hTarget := coefficientBaseEquiv_compact χ hG K hK ψ' hψ' hψ'K τ a z
    (genericComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A pA qA zA v)
  have hTensor := congrArg (fun T => T (compactTensorEquiv χ hG K hK ψ hψ hψK A (τ * z) v))
    (compactTensorSquare χ hG K hK ψ hψ hψK ψ' hψ' hψ'K τ a pA qA pB qB z hA hB
      hForward hReverse)
  exact hBJ.trans ((congrArg
    (compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K B pB qB zB) hSource).trans
      (hTensor.trans ((congrArg
        (compactTensorBaseEquiv χ K hK ψ' hψ' τ a) hAJ).symm.trans hTarget.symm)))

end TensorSquare

end Langlands.Plancherel.ActualNormalizedTensorBaseChange
