import Langlands.GroupScheme.SimplyConnected.InnerTypeANormOneStatement
import Langlands.GroupScheme.CentralSimpleNormOneDivisionModel

/-!
# Conditional binary models for inner type A of split rank one

This composes the two explicit, unproved structural inputs with the
constructed division-matrix model. It does not assert either input or
determine the types of arbitrary local rank-one groups.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The inner-type-A identification and matrix-rank formula imply the
actual binary norm-one model for an inner-type-A group of split rank one,
over any field. Both structural statements remain explicit hypotheses. -/
theorem exists_binary_model_of_innerTypeA
    (hinner : InnerTypeANormOneStatement.{u})
    (hrank : CentralSimpleUnits.MatrixNormOneSplitRankStatement.{u})
    {K : Type u} [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ)
    (hsc : IsSimplyConnected G) (ha : IsAbsolutelyAlmostSimple G)
    (htype : d.HasInnerTypeA n) (hG : splitRank G = 1) :
    ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
      (_ : FiniteDimensional K D) (_ : Algebra.IsCentral K D),
      Nonempty (G ≅ CentralSimpleUnits.BinaryRoot.groupScheme K D) := by
  obtain ⟨A, hA, hKA, hfd, hcentral, hsimple, _hdegree, ⟨e⟩⟩ :=
    hinner K G d n hsc ha htype
  exact CentralSimpleUnits.exists_binary_model_of_normOne_presentation K A hrank e hG

/-- Actual binary norm-one presentation data. This is output data,
including a group-scheme isomorphism, rather than an assumed type label. -/
structure BinaryNormOnePresentation (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) where
  divisionAlgebra : Type u
  [divisionRing : DivisionRing divisionAlgebra]
  [algebra : Algebra K divisionAlgebra]
  [finiteDimensional : FiniteDimensional K divisionAlgebra]
  [central : Algebra.IsCentral K divisionAlgebra]
  iso : G ≅ CentralSimpleUnits.BinaryRoot.groupScheme K divisionAlgebra

attribute [instance] BinaryNormOnePresentation.divisionRing
  BinaryNormOnePresentation.algebra BinaryNormOnePresentation.finiteDimensional
  BinaryNormOnePresentation.central

/-- Choose an actual binary presentation using the two explicit structural
inputs and the given actual inner-type-A index. -/
def innerTypeABinaryPresentation
    (hinner : InnerTypeANormOneStatement.{u})
    (hrank : CentralSimpleUnits.MatrixNormOneSplitRankStatement.{u})
    {K : Type u} [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ)
    (hsc : IsSimplyConnected G) (ha : IsAbsolutelyAlmostSimple G)
    (htype : d.HasInnerTypeA n) (hG : splitRank G = 1) :
    BinaryNormOnePresentation K G := Classical.choice <| by
  obtain ⟨D, hD, hKD, hfd, hcentral, ⟨e⟩⟩ :=
    exists_binary_model_of_innerTypeA hinner hrank G d n hsc ha htype hG
  exact ⟨⟨D, e⟩⟩

end Langlands.GroupScheme
