import Langlands.Representation.Plancherel.ActualCommonLeviTensor
import Langlands.Representation.Plancherel.ActualCommonLeviV3Statement
import Langlands.Representation.Plancherel.DynamicCommonLeviContinuationStatement
import Langlands.Representation.Smooth.Contragredient.FiniteLengthProof
import Langlands.Representation.Smooth.IrreducibleRealization

/-! # Actual continued pairs from common-Levi continuation existence -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviV3

open Aubert.General DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor

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
  leviLocallyCompact

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
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

/-- Choose the actual continued pair from the common-Levi existence statement. -/
def continuedPairOfContinuation
    (hc : ConditionalDynamicCommonLeviContinuationStatement.{u, uV})
    (hA : A.IsAdmissible) (hfinite : A.HasFiniteLength) :
    ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A :=
  Classical.choice (by
    obtain ⟨hmod, Ω, hΩ, hne, hconv, _, ⟨pres⟩⟩ :=
      hc F G hG χ K hK ψ hψ hψK ψ' hψ' hψ'K A hA hfinite
    exact ⟨⟨hmod, Ω, hΩ, hne, hconv, pres⟩⟩)

/-- The one common-Levi existence theorem supplies both directions on the
inducing object and on its smooth dual. -/
theorem nonempty_continuedPairs_of_continuation
    (hc : ConditionalDynamicCommonLeviContinuationStatement.{u, uV})
    (hA : A.IsAdmissible) (hi : A.representation.IsIrreducible) :
    Nonempty (ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A) ∧
    Nonempty (ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A) ∧
    Nonempty (ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A.contragredient) ∧
    Nonempty (ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient) := by
  have hfinite := SmoothRep.hasFiniteLength_of_isIrreducible hi
  have hcof := compactOpenCofinal_of_nonarchimedean (levi χ)
  have hdual := (SmoothRep.isAdmissible_contragredient_iff hcof A).mpr hA
  have hdualFinite := SmoothRep.contragredient_hasFiniteLength hcof A hA hfinite
  exact ⟨⟨continuedPairOfContinuation χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A hc hA hfinite⟩,
    ⟨continuedPairOfContinuation χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A hc hA hfinite⟩,
    ⟨continuedPairOfContinuation χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A.contragredient
      hc hdual hdualFinite⟩,
    ⟨continuedPairOfContinuation χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient
      hc hdual hdualFinite⟩⟩

end Langlands.Plancherel.ActualCommonLeviV3
