import Langlands.Representation.Plancherel.ActualCommonLeviCoherenceReduction
import Langlands.Representation.Plancherel.ActualCommonLeviCoefficientInjectivity
import Langlands.Representation.Plancherel.ActualCommonLeviUnitaryIrreducibilityStatement
import Langlands.Representation.Plancherel.ActualCommonLeviUnitaryIrreducibilityProof

/-! # Closed common-Levi coherence from V.3.1 and dense unitary irreducibility -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviCoherence

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviRationalTensor
open ActualCommonLeviV3 UnramifiedOperatorFamily

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

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)

local notation "Xu" => unitaryUnramifiedCharacters (normCharacters χ)

variable
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
  (qMeasure : Measure (levi χ ⧸ C)) [qMeasure.IsHaarMeasure] [qMeasure.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation qMeasure)
  (hi : A.representation.IsIrreducible)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))

local notation "Par" => ParabolicPresentation χ K

omit [BorelSpace (levi χ ⧸ C)] [qMeasure.IsInvInvariant] in
include hi in
/-- Dense unitary irreducibility of the actual normalized inductions gives
dense coefficient injectivity for every structural presentation. -/
theorem dense_injective_of_denseUnitaryIrreducibility
    (hirr : DenseUnitaryIrreducibilityStatement χ A C hC qMeasure)
    (hcenter : IsActualSplitCenter χ C) (P : Par) :
    Dense {z : Xu |
      Function.Injective (presentationCoefficientMap χ hG A C hC qMeasure hsq K hK P z)} :=
  (hirr hG hsq hi hcenter P.cocharacter P.centralizer_eq).mono fun z hz =>
    coefficientMap_injective_of_isIrreducible χ hG A C hC qMeasure hsq K hK
      P.cocharacter P.centralizer_eq P.iwasawa z hz

/-- Closed common-Levi coherence from the pairwise closed V.3.1 statements and
dense unitary irreducibility of the actual normalized inductions. -/
theorem closedCommonLeviCoherence_of_v31_of_denseUnitaryIrreducibility
    (hV31 : ∀ P Q : Par, ClosedV31Statement χ hG A C hC qMeasure hsq hi K hK
      P.cocharacter P.centralizer_eq P.iwasawa Q.cocharacter Q.centralizer_eq Q.iwasawa)
    (hirr : DenseUnitaryIrreducibilityStatement χ A C hC qMeasure) :
    ClosedCommonLeviCoherenceStatement χ hG A C hC qMeasure hsq hi K hK :=
  closedCommonLeviCoherence_of_v31_of_dense_injective χ hG A C hC qMeasure hsq hi K hK hV31
    (dense_injective_of_denseUnitaryIrreducibility χ hG A C hC qMeasure hsq hi K hK hirr)

/-- Closed common-Levi coherence from the pairwise closed V.3.1 statements alone:
the dense unitary irreducibility input is the published theorem
`ActualCommonLeviV3.denseUnitaryIrreducibility`. -/
theorem closedCommonLeviCoherence_of_v31
    (hV31 : ∀ P Q : Par, ClosedV31Statement χ hG A C hC qMeasure hsq hi K hK
      P.cocharacter P.centralizer_eq P.iwasawa Q.cocharacter Q.centralizer_eq Q.iwasawa) :
    ClosedCommonLeviCoherenceStatement χ hG A C hC qMeasure hsq hi K hK :=
  closedCommonLeviCoherence_of_v31_of_denseUnitaryIrreducibility χ hG A C hC qMeasure hsq hi K hK
    hV31 (denseUnitaryIrreducibility χ A C hC qMeasure)

end Langlands.Plancherel.ActualCommonLeviCoherence
