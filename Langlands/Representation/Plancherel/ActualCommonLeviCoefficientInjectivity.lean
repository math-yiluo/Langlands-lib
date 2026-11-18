import Langlands.Representation.Plancherel.ActualCommonLeviV3Statement
import Langlands.Representation.Plancherel.CoefficientTensorInjectivity
import Langlands.Representation.Aubert.General.RationalInductionDualityReduction

/-! # Injectivity of the actual common-Levi coefficient map at irreducible points -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal TensorProduct
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
  ambientMeasurable ambientBorel leviMeasurable leviBorel leviLocallyCompact
  parabolicLocallyCompact radicalLocallyCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
  (qMeasure : Measure (levi χ ⧸ C)) [qMeasure.IsHaarMeasure] [qMeasure.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation qMeasure)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

/-- The actual normalized induction underlying the coefficient fiber at a
unitary parameter. -/
abbrev unitaryNormalizedInduction
    (z : unitaryUnramifiedCharacters (normCharacters χ)) :=
  (normalizedInductionFunctor (commonDecomposition χ ψ hψ) (radical_isClosed ψ)).obj
    (twistObject χ (unitaryParameter χ z) A)

include hK hψK hsq in
omit [BorelSpace (levi χ ⧸ C)] [qMeasure.IsInvInvariant] in
/-- At a unitary parameter where the actual normalized induction is
irreducible, the actual coefficient map is injective. -/
theorem coefficientMap_injective_of_isIrreducible
    (z : unitaryUnramifiedCharacters (normCharacters χ))
    (hirr : (unitaryNormalizedInduction χ A ψ hψ z).representation.IsIrreducible) :
    Function.Injective (coefficientMap χ hG A C hC qMeasure hsq K hK ψ hψ hψK z) := by
  let := quotientCompact K hK ψ hψK
  have hadm : (unitaryNormalizedInduction χ A ψ hψ z).IsAdmissible :=
    normalizedInductionFunctor_obj_isAdmissible (commonDecomposition χ ψ hψ)
      (radical_isClosed ψ) (commonProjection_continuous χ ψ hψ) _
      (unitaryTwist_squareIntegrable χ A C hC qMeasure hsq z).1
  have hinj := coefficientTensorMap_injective _ hadm hirr
  intro x y hxy
  apply (CompactInduction.leviCoefficientTensorEquiv (commonDecomposition χ ψ hψ)
    (radical_isClosed ψ) (twistObject χ (unitaryParameter χ z) A) K
    (DynamicOppositeCanonicalScalar.radical_unimodular ψ hG) hK
    (DynamicOppositeCanonicalScalar.parabolic_isClosed ψ)
    (commonProjection_continuous χ ψ hψ) (iwasawa_sets K ψ hψK)
    (ambient_modularCharacter hG) (common_modularCharacter χ hG ψ hψ)
    (unitaryTwist_squareIntegrable χ A C hC qMeasure hsq z).1).toLinearEquiv.injective
  exact hinj hxy

end Langlands.Plancherel.ActualCommonLeviV3
