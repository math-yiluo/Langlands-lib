import Langlands.Representation.Plancherel.ActualCommonLeviRationalTensor
import Langlands.Representation.Plancherel.ActualConjugateLeviTensor

/-! # Whole-operator denominators under actual parameter conjugation -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

universe u uV uW

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal BigOperators
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel
namespace UnramifiedOperatorFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H J : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [IsAffine J.X.left]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (e : H ≅ J)

local instance sourceTopology : TopologicalSpace (rationalPoints H) :=
  rationalPointTopology F H.X
local instance targetTopology : TopologicalSpace (rationalPoints J) :=
  rationalPointTopology F J.X

set_option hygiene false in
local notation "XH" => unramifiedCharacters (fun a => (rationalNormCharacters H a).toMul)
set_option hygiene false in
local notation "XJ" => unramifiedCharacters (fun a => (rationalNormCharacters J a).toMul)
set_option hygiene false in
local notation "RJ" => unramifiedRegularFunctions (fun a => (rationalNormCharacters J a).toMul)

variable {U : Set XJ}

local notation "pull" => Set.restrictPreimage U (rationalUnramifiedCharacterTransport e)

/-- Each regular coefficient in the finite numerator expansion is pulled
back by the actual isomorphism of the full rational-character algebras. -/
theorem IsPolynomialOn.parameterPullback {f : U → V} (hf : IsPolynomialOn U f) :
    IsPolynomialOn (rationalUnramifiedCharacterTransport e ⁻¹' U) (f ∘ pull) := by
  obtain ⟨n, b, v, h⟩ := hf
  refine ⟨n, fun i => (rationalUnramifiedRegularFunctionsEquiv e).symm (b i), v, ?_⟩
  intro z
  simpa only [Function.comp_def, Set.restrictPreimage, Set.MapsTo.restrict, Subtype.map, rationalUnramifiedRegularFunctionsEquiv_symm_val] using h (pull z)

/-- The pulled-back denominator clears the entire pulled-back operator with
its original numerator expansion transported coefficient by coefficient. -/
theorem parameterPullback_clears {T : U → V →ₗ[ℂ] W} (b : RJ)
    (hT : IsPolynomialOperatorOn U (fun z => b.val z.val • T z)) :
    IsPolynomialOperatorOn (rationalUnramifiedCharacterTransport e ⁻¹' U)
      (fun z => ((rationalUnramifiedRegularFunctionsEquiv e).symm b).val z.val • T (pull z)) := by
  intro v
  simpa only [Function.comp_def, Set.restrictPreimage, Set.MapsTo.restrict, Subtype.map, rationalUnramifiedRegularFunctionsEquiv_symm_val] using
    (hT v).parameterPullback e

/-- Rationality on a genuine locus is retained under the actual pullback,
with a single denominator on the whole preimage. -/
theorem IsRationalOperatorOn.parameterPullback {T : U → V →ₗ[ℂ] W}
    (hT : IsRationalOperatorOn U T) :
    IsRationalOperatorOn (rationalUnramifiedCharacterTransport e ⁻¹' U) (T ∘ pull) := by
  obtain ⟨b, hb, ht⟩ := hT
  refine ⟨(rationalUnramifiedRegularFunctionsEquiv e).symm b, fun z => ?_,
    parameterPullback_clears e b ht⟩
  simpa only [Set.restrictPreimage, Set.MapsTo.restrict, Subtype.map, rationalUnramifiedRegularFunctionsEquiv_symm_val] using hb (pull z)

end UnramifiedOperatorFamily

namespace ActualConjugateLeviRationalParameter

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviRationalTensor
open ActualConjugateLeviTwist UnramifiedOperatorFamily

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
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (g : RationalPoint F G.X)
  (hG : IsConnectedReductive G) (A : SmoothRep.{0, u, uV} ℂ (levi χ))

set_option hygiene false in
set_option quotPrecheck false in
local notation "χg" => (χ ≫ (G.innerIso g).hom)
set_option hygiene false in
local notation "gA" => conjugateRepresentation χ g A

variable (K' : OpenSubgroup (RationalPoint F G.X))
  (hK' : IsCompact (K' : Set (RationalPoint F G.X)))
  (hχgK' : ∀ x : RationalPoint F G.X, ∃ p : parabolic χg, ∃ k : K',
    x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χg)
  (hψK' : ∀ x : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K',
    x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ContinuedPair χg hG K' hK' χg rfl hχgK' ψ hψ hψK' gA)
  (q : ContinuedPair χg hG K' hK' ψ hψ hψK' χg rfl hχgK' (gA).contragredient)

set_option hygiene false in
local notation "D" => ActualConjugateLeviTensor.genericLocus χ g hG A K' hK' hχgK' ψ hψ hψK' p q

/-- The actual same-Levi standard tensor after the translation is indexed
on the original parameter space through full character conjugation. -/
def pulledBackStandardTensor (z : D) :
    compactFiber χg K' χg rfl gA →ₗ[ℂ] compactFiber χg K' ψ hψ gA :=
  compactComparison χg hG K' hK' χg rfl hχgK' ψ hψ hψK' gA p q
    (ActualConjugateLeviTensor.genericParameter χ g hG A K' hK' hχgK' ψ hψ hψK' p q z)

/-- Whole-operator rationality for the particular pulled-back tensor of the
actual forward operator and inverse reverse-dual operator. -/
theorem pulledBackStandardTensor_rational
    (d : ScalarInverseData χg hG K' hK' χg rfl hχgK' ψ hψ hψK' gA p q) :
    IsRationalOperatorOn D (pulledBackStandardTensor χ g hG A K' hK' hχgK' ψ hψ hψK' p q) := by
  have h := compactComparison_rational χg hG K' hK' χg rfl hχgK' ψ hψ hψK' gA p q d
  exact IsRationalOperatorOn.parameterPullback (H := parameterScheme χ) (J := parameterScheme χg)
    (parameterConjugationIso χ g) h

end ActualConjugateLeviRationalParameter
end Langlands.Plancherel
