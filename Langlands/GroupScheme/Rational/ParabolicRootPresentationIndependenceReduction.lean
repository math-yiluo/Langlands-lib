import Langlands.GroupScheme.Rational.ParabolicRootPresentationSimpleRoots
import Langlands.GroupScheme.Rational.ParabolicRootPresentationTransport
import Langlands.GroupScheme.Rational.ReflectionStandardCocharacter

/-! # Full presentation independence from actual root reflections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

/-- Actual reflection existence suffices for full independence and both-direction
component transport. The geometric existence premise is retained explicitly. -/
def ParabolicRootPresentationReflectionReductionStatement : Prop :=
  RelativeRootReflectionExistenceStatement.{u} →
    ParabolicRootPresentationIndependenceStatement.{u} ∧
      ParabolicRootPresentationIsoStatement.{u}

namespace ParabolicRootPresentation

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M P : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r s : ParabolicRootPresentation p l a)

/-- Equality of the intrinsic simple support gives unrestricted restricted-root
independence once both ambient root hypotheses are supplied. -/
theorem restrictedRoots_eq_of_simpleRoot_hypotheses
    (hLIr : LinearIndependent ℚ (fun alpha : simpleRelativeRoots r.data.i r.data.ν =>
      toRat (alpha : characterLattice r.data.T)))
    (hLIs : LinearIndependent ℚ (fun alpha : simpleRelativeRoots s.data.i s.data.ν =>
      toRat (alpha : characterLattice s.data.T)))
    (hnegr : ∀ alpha ∈ relativeRoots r.data.i, -alpha ∈ relativeRoots r.data.i)
    (hnegs : ∀ alpha ∈ relativeRoots s.data.i, -alpha ∈ relativeRoots s.data.i) :
    r.restrictedRoots = s.restrictedRoots := by
  rw [r.restrictedRoots_eq_image_intrinsicSimpleRoots hLIr hnegr,
    s.restrictedRoots_eq_image_intrinsicSimpleRoots hLIs hnegs,
    r.intrinsicSimpleRoots_eq s]

end ParabolicRootPresentation

/-- Actual integral reflection data supply both rational independence and
negation at each of the two unrelated maximal split tori. -/
theorem parabolicRootPresentationIndependenceStatement_of_reflections
    (hreflect : RelativeRootReflectionExistenceStatement.{u}) :
    ParabolicRootPresentationIndependenceStatement.{u} := by
  intro k _ G hG P M A p l a
  have := hG.isAffineHom
  have := hG.smooth
  intro r s
  have := r.isCompatible.maximalSplit.isSplitSubtorus.mono
  have := s.isCompatible.maximalSplit.isSplitSubtorus.mono
  obtain ⟨Dr, _⟩ := hreflect k G hG r.data.T r.data.i r.isCompatible.maximalSplit
  obtain ⟨Ds, _⟩ := hreflect k G hG s.data.T s.data.i s.isCompatible.maximalSplit
  have hTr := r.isCompatible.maximalSplit.isSplitSubtorus.1
  have hTs := s.isCompatible.maximalSplit.isSplitSubtorus.1
  have hroot := r.restrictedRoots_eq_of_simpleRoot_hypotheses s
    (Dr.linearIndependent_simpleRelativeRoots r.data.i r.data.ν hTr
      (hTr.finite_relativeRoots r.data.i) r.isCompatible.generic)
    (Ds.linearIndependent_simpleRelativeRoots s.data.i s.data.ν hTs
      (hTs.finite_relativeRoots s.data.i) s.isCompatible.generic)
    (fun _ h => Dr.neg_mem_relativeRoots r.data.i h)
    (fun _ h => Ds.neg_mem_relativeRoots s.data.i h)
  exact ⟨hroot, r.cones_eq_of_restrictedRoots_eq s hroot⟩

/-- The six component pullback equalities follow without an independent
conjugacy or presentation-existence assumption. -/
theorem parabolicRootPresentationIsoStatement_of_reflections
    (hreflect : RelativeRootReflectionExistenceStatement.{u}) :
    ParabolicRootPresentationIsoStatement.{u} :=
  parabolicRootPresentationIsoStatement_of_independence
    (parabolicRootPresentationIndependenceStatement_of_reflections hreflect)

/-- The exact aggregate follows from actual reflection existence and the exact
specified-map presentation-existence proposition. Both inputs stay explicit. -/
theorem parabolicRootPresentationStatement_of_existence_of_reflections
    (hexists : ParabolicRootPresentationExistenceStatement.{u})
    (hreflect : RelativeRootReflectionExistenceStatement.{u}) :
    ParabolicRootPresentationStatement.{u} :=
  parabolicRootPresentationStatement_iff_existence_independence.mpr
    ⟨hexists, parabolicRootPresentationIndependenceStatement_of_reflections hreflect⟩

/-- The full arbitrary-universe conditional independence and transport reduction. -/
theorem parabolicRootPresentationReflectionReduction :
    ParabolicRootPresentationReflectionReductionStatement.{u} :=
  fun hreflect =>
    ⟨parabolicRootPresentationIndependenceStatement_of_reflections hreflect,
      parabolicRootPresentationIsoStatement_of_reflections hreflect⟩

end Langlands.GroupScheme
