import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyReduction
import Langlands.GroupScheme.Rational.SolvableMaximalSplitTorusStatement
import Langlands.GroupScheme.Rational.SmoothClosedSubgroupInduction

/-! # Closed subgroup descent for maximal split torus conjugacy -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- Every split subtorus of the ambient group factors through this inclusion. -/
def SplitToriFactorThrough {H G : GroupScheme (Spec (CommRingCat.of k))}
    (j : H ⟶ G) : Prop :=
  ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
    IsSplitSubtorus i → ∃ f : T.toGrp ⟶ H, f ≫ j = i

/-- Every split subtorus of the ambient group can be rationally conjugated into
this inclusion. -/
def SplitToriConjugateInto {H G : GroupScheme (Spec (CommRingCat.of k))}
    (j : H ⟶ G) : Prop :=
  ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
    IsSplitSubtorus i →
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
      (f : T.toGrp ⟶ H), f ≫ j = i ≫ (G.innerIso g).hom

/-- The two structural branches used to prove smooth-group maximal split torus
conjugacy: a common solvable closed overgroup, or conjugation into a proper
smooth connected affine closed subgroup. -/
def SmoothMaximalSplitTorusDescentStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    (∃ (H : GroupScheme (Spec (CommRingCat.of k)))
      (_ : Smooth H.X.hom) (_ : IsAffineHom H.X.hom) (_ : ConnectedSpace H.X.left)
      (j : H ⟶ G), IsClosedSubgroup j ∧ IsSolvableGroupScheme H ∧
        SplitToriFactorThrough j) ∨
    (∃ (H : GroupScheme (Spec (CommRingCat.of k)))
      (_ : Smooth H.X.hom) (_ : IsAffineHom H.X.hom) (_ : ConnectedSpace H.X.left)
      (j : H ⟶ G), IsClosedSubgroup j ∧ ¬ IsIso j ∧ SplitToriConjugateInto j)

/-- Noetherian closed-subgroup induction assembles the solvable theorem and
the structural descent statement into the exact smooth-group conjugacy target. -/
theorem smoothMaximalSplitTorusConjugacy_of_solvable_of_descent
    (hsolv : SolvableMaximalSplitTorusConjugacyStatement.{u})
    (hdescent : SmoothMaximalSplitTorusDescentStatement.{u}) :
    SmoothMaximalSplitTorusConjugacyStatement.{u} := by
  rw [smoothMaximalSplitTorusConjugacyStatement_iff]
  intro k _ G _ _ _
  have hG : ConnectedSpace G.X.left → MaximalSplitToriAreConjugate G := by
    apply smoothAffineGroup_closedSubgroup_induction
      (fun H => ConnectedSpace H.X.left → MaximalSplitToriAreConjugate H) ?_ G
    intro H _ _ ih hconn
    let : ConnectedSpace H.X.left := hconn
    rcases hdescent k H with hA | hB
    · obtain ⟨K, hsm, haf, hco, j, hj, hsolvK, hfactor⟩ := hA
      let : Smooth K.X.hom := hsm
      let : IsAffineHom K.X.hom := haf
      let : ConnectedSpace K.X.left := hco
      intro T T' i i' hi hi'
      obtain ⟨f, hf⟩ := hfactor T i hi.isSplitSubtorus
      obtain ⟨f', hf'⟩ := hfactor T' i' hi'.isSplitSubtorus
      exact subgroupConjugate_of_closed_factorizations (hsolv k K hsolvK)
        j hj hi hi' f f' hf hf'
    · obtain ⟨K, hsm, haf, hco, j, hj, hproper, hlift⟩ := hB
      let : Smooth K.X.hom := hsm
      let : IsAffineHom K.X.hom := haf
      exact MaximalSplitToriAreConjugate.of_closed_overgroup
        (ih K j hj hproper hco) j hj (fun T i hi => hlift T i hi.isSplitSubtorus)
  exact hG inferInstance

end Langlands.GroupScheme
