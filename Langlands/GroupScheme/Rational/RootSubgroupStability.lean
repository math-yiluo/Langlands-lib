import Langlands.GroupScheme.Rational.RootSubgroupStabilityProof

/-! # Stability of the intrinsic relative-root subgroup functor -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {B : Scheme.{u}} {H G : GroupScheme B}

/-- Evaluation at zero commutes with an action by a point pulled back from the test. -/
theorem evalZero_act (b : AutomorphicAction H G) {T : Over B}
    (h : T ⟶ H.X) (e : T ⊗ AffineLine.scheme B ⟶ G.X) :
    Dynamic.evalZero (b.act (fst T (AffineLine.scheme B) ≫ h) e) =
      b.act h (Dynamic.evalZero e) := by
  simp only [Dynamic.evalZero, b.naturality, lift_fst_assoc, Category.id_comp]

end AutomorphicAction

namespace RelativeRoot

variable {B : Scheme.{u}} {S : CommGroupScheme B} {G : GroupScheme B}
    (i : S.toGrp ⟶ G) (a : characterLattice S)

/-- The torus image normalizes the intrinsic relative-root functor on all tests. -/
theorem subgroup_isNormalizedBy_range :
    (subgroup i a).IsNormalizedBy (SubgroupFunctor.range i) := by
  intro T s g hs hg
  obtain ⟨s, rfl⟩ := SubgroupFunctor.mem_range.mp hs
  simpa only [AutomorphicAction.conjugation_act] using subgroup_isStable i a T s g hg

section Represented

variable {U : GroupScheme B} (j : U ⟶ G) (hj : (subgroup i a).IsRepresentedBy j)

/-- The actual full-torus action on any representative of the intrinsic root functor. -/
def subgroupAction : AutomorphicAction S.toGrp U :=
  AutomorphicAction.onRepresentedSubgroup (AutomorphicAction.conjugation i) j hj
    (subgroup_isStable i a)

/-- The representing inclusion intertwines the constructed action with conjugation. -/
theorem subgroupAction_act_comp {T : Over B} (s : T ⟶ S.X) (g : T ⟶ U.X) :
    (subgroupAction i a j hj).act s g ≫ j.hom.hom =
      (s ≫ i.hom.hom) * (g ≫ j.hom.hom) * (s ≫ i.hom.hom)⁻¹ := by
  rw [subgroupAction, AutomorphicAction.onRepresentedSubgroup_act_comp,
    AutomorphicAction.conjugation_act]

end Represented

end RelativeRoot

end Langlands.GroupScheme
