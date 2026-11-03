import Langlands.GroupScheme.Rational.WeightSemigroupStatement
import Langlands.GroupScheme.Rational.Characters

/-! # Central stable vector subgroups of split unipotent groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- A nontrivial smooth connected split unipotent group has a positive-dimensional
central vector subgroup stable under an actual action of any smooth affine group.
The induced action is retained, without requiring it to be linear. -/
def SplitUnipotentStableVectorSubgroupStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (U : GroupScheme (Spec (CommRingCat.of k))),
    Smooth U.X.hom → IsAffineHom U.X.hom → ConnectedSpace U.X.left →
    IsUnipotent U → IsSplitUnipotent U → SubgroupFunctor.range (𝟙 U) ≠ ⊥ →
    ∀ (H : GroupScheme (Spec (CommRingCat.of k))),
    Smooth H.X.hom → IsAffineHom H.X.hom → ∀ a : AutomorphicAction H U,
      ∃ (V : GroupScheme (Spec (CommRingCat.of k))) (z : V ⟶ U)
        (aV : AutomorphicAction H V) (n : ℕ)
        (e : ∀ T : Over (Spec (CommRingCat.of k)),
          (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤))),
        IsClosedSubgroup z ∧ Smooth V.X.hom ∧ IsAffineHom V.X.hom ∧
        ConnectedSpace V.X.left ∧ IsUnipotent V ∧ IsSplitUnipotent V ∧
        IsCentral z ∧ a.IsStable (SubgroupFunctor.range z) ∧
        SubgroupFunctor.range z ≠ ⊥ ∧ 0 < n ∧
        SmoothOfRelativeDimension n V.X.hom ∧ IsNaturalVectorCoordinates e ∧
        ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (v : T ⟶ V.X),
          aV.act h v ≫ z.hom.hom = a.act h (v ≫ z.hom.hom)

end Langlands.GroupScheme.RelativeRoot
