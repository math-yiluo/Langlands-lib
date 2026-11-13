import Langlands.Representation.Plancherel.RationalNormKernelRemarksStatements
import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.Analysis.Local.NormalSubgroupModularCharacter

/-! # Proof of Renard V.2.3: the norm kernel `⁰G` is unimodular -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

/-- Renard V.2.3, Proposition: `⁰G` is unimodular. -/
theorem rationalNormKernelUnimodular : RationalNormKernelUnimodularStatement.{u} := by
  intro F _ _ _ _ G hG _ _ _ h
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have hH : IsClosed (rationalCommonNormKernel G : Set (GroupScheme.rationalPoints G)) :=
    isClosed_rationalCommonNormKernel G
  let : MeasurableSpace (GroupScheme.rationalPoints G) := borel _
  have : BorelSpace (GroupScheme.rationalPoints G) := ⟨rfl⟩
  let : MeasurableSpace (rationalCommonNormKernel G) := borel _
  have : BorelSpace (rationalCommonNormKernel G) := ⟨rfl⟩
  let : MeasurableSpace
      (QuotientIntegration.LeftQuotient (rationalCommonNormKernel G)) := borel _
  have : BorelSpace
      (QuotientIntegration.LeftQuotient (rationalCommonNormKernel G)) := ⟨rfl⟩
  let : MeasurableSpace
      (GroupScheme.rationalPoints G ⧸ rationalCommonNormKernel G) := borel _
  have : BorelSpace
      (GroupScheme.rationalPoints G ⧸ rationalCommonNormKernel G) := ⟨rfl⟩
  have key := QuotientIntegration.modularCharacter_normalSubgroup
    (rationalCommonNormKernel G) hH h
  refine key.trans ?_
  exact Aubert.General.RationalPointFamily.rationalReductiveUnimodularity F G hG
    standardCocharacter (h : GroupScheme.rationalPoints G)

end Langlands.Plancherel
