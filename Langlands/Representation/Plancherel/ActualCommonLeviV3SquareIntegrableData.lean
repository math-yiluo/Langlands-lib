import Langlands.Representation.Plancherel.ActualCommonLeviUnitaryContinuation
import Langlands.Representation.Plancherel.ActualCommonLeviV3GenericData
import Langlands.Representation.Unitary.ConjugateEquiv

/-! # The genuine generic comparison for the square-integrable inducing data -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option quotPrecheck false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Topology
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviV3

open Aubert.General Induction DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor UnramifiedOperatorFamily
open CompactInduction

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
  ambientMeasurable ambientBorel leviMeasurable leviBorel
  leviLocallyCompact parabolicLocallyCompact

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
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

variable
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

private theorem isUnitarizable_contragredient_of_isUnitarizable
    (hadm : A.IsAdmissible) (hunit : IsUnitarizable A.representation) :
    IsUnitarizable A.contragredient.representation := by
  obtain ⟨b⟩ := hunit
  let hcof := compactOpenCofinal_of_nonarchimedean (levi χ)
  let e := b.smoothDualEquiv hcof hadm
  exact (isUnitarizable_iff_of_conjugateEquiv
    (ρ := A.representation) (σ := A.contragredient.representation) e
    (b.toSmoothDual_apply_action hadm.1)).mp ⟨b⟩

/-- The square-integrable inducing data themselves give all three actual
continuations for the genuine generic comparison. -/
def genericComparisonDataOfSquareIntegrable
    (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation qMeasure)
    (hi : A.representation.IsIrreducible) (hsplit : IsActualSplitCenter χ C) :
    GenericComparisonData χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A := by
  let hcof := compactOpenCofinal_of_nonarchimedean (levi χ)
  have hunit := HarishChandraSchwartz.isUnitarizable_of_isSquareIntegrableModCentralSubgroup
    C hC qMeasure hcof hsq
  have hfin := SmoothRep.hasFiniteLength_of_isIrreducible hi
  have hdu := isUnitarizable_contragredient_of_isUnitarizable χ A hsq.1 hunit
  have hda := (SmoothRep.isAdmissible_contragredient_iff hcof A).mpr hsq.1
  have hdf := SmoothRep.contragredient_hasFiniteLength hcof A hsq.1 hfin
  let p := continuedPairOfUnitarizable χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A hsq.1 hfin hunit
  let q := continuedPairOfUnitarizable χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient hda hdf hdu
  let s := continuedPairOfUnitarizable χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A.contragredient hda hdf hdu
  exact genericComparisonDataOfActualContinuations χ hG K hK ψ hψ hψK ψ' hψ' hψ'K
    A p q s C hC qMeasure hsq hi hsplit

end Langlands.Plancherel.ActualCommonLeviV3
