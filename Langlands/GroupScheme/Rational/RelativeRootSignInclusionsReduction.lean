import Langlands.GroupScheme.Rational.WeightSemigroupSupport
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsStatement
import Langlands.GroupScheme.Rational.RelativeRootSignSupport

/-! # Semigroup reductions for dynamic subgroup inclusion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Exact realization and dynamic comparison reduce parabolic inclusion to
containment of the nonnegative regions on actual ambient action weights. -/
theorem dynamic_parabolic_le_iff_on_weightSupport_of_semigroup
    (hReal : SemigroupRealizationStatement.{u})
    (hDynamic : DynamicSemigroupComparisonStatement.{u})
    (hSmooth : Smooth G.X.hom) (hConn : ConnectedSpace G.X.left)
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (zeta eta : cocharacterLattice S) :
    Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) ≤
        Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ↔
      ∀ χ ∈ actionWeightSupport (AutomorphicAction.conjugation i) ⊤,
        χ ∈ nonnegativeSemigroup zeta → χ ∈ nonnegativeSemigroup eta := by
  have hz := hDynamic k G hSmooth inferInstance hConn S hS i zeta
  have he := hDynamic k G hSmooth inferInstance hConn S hS i eta
  rw [hz.1, he.1]
  have hr := hReal k G hSmooth inferInstance S hS (AutomorphicAction.conjugation i)
  have hrz := hr (nonnegativeSemigroup zeta)
  have hre := hr (nonnegativeSemigroup eta)
  exact semigroupSubgroup_le_iff_on_weightSupport _ hrz.2.2.1
    ((hre.2.2.2.2.1 _ hre.1 hre.2.1).mpr le_rfl)

/-- Dynamic comparison and generator monotonicity suffice for positive-support
inclusion; no exact-Lie-image hypothesis is needed in this direction. -/
theorem dynamic_unipotent_le_of_on_weightSupport_of_semigroup
    (hDynamic : DynamicSemigroupComparisonStatement.{u})
    (hSmooth : Smooth G.X.hom) (hConn : ConnectedSpace G.X.left)
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (zeta eta : cocharacterLattice S)
    (h : ∀ χ ∈ actionWeightSupport (AutomorphicAction.conjugation i) ⊤,
      χ ∈ positiveSemigroup zeta → χ ∈ positiveSemigroup eta) :
    Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) ≤
      Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i) := by
  have hz := hDynamic k G hSmooth inferInstance hConn S hS i zeta
  have he := hDynamic k G hSmooth inferInstance hConn S hS i eta
  rw [hz.2.2, he.2.2]
  exact semigroupSubgroup_mono_on_weightSupport _ h

end Langlands.GroupScheme.RelativeRoot

namespace Langlands.GroupScheme

/-- The structural semigroup realization and dynamic comparison propositions
suffice for the exact actual-root sign inclusion target. -/
def RelativeRootSignInclusionsFromSemigroups : Prop :=
  RelativeRoot.SemigroupRealizationStatement.{u} →
  RelativeRoot.DynamicSemigroupComparisonStatement.{u} →
  RelativeRootSignInclusionsStatement.{u}

/-- Conditional structural assembly. Both structural propositions remain
explicit premises; this is not the unconditional target theorem. -/
theorem relativeRootSignInclusions_of_semigroupRealization :
    RelativeRootSignInclusionsFromSemigroups.{u} := by
  intro hReal hDynamic k _ G hG T i hi zeta eta
  haveI := hG.isAffineHom
  constructor
  · exact (RelativeRoot.dynamic_parabolic_le_iff_on_weightSupport_of_semigroup
      hReal hDynamic hG.smooth hG.connectedSpace hi.1.1 i zeta eta).trans
        (RelativeRoot.nonnegative_rootSupport_iff i zeta eta).symm
  · intro h
    exact RelativeRoot.dynamic_unipotent_le_of_on_weightSupport_of_semigroup
      hDynamic hG.smooth hG.connectedSpace hi.1.1 i zeta eta
        ((RelativeRoot.positive_rootSupport_iff i zeta eta).mp h)

end Langlands.GroupScheme
