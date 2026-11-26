import Langlands.GroupScheme.Rational.CharacterBaseChange
import Langlands.GroupScheme.Rational.LeviSubgroup
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Split components of nested Levi subgroups over a field extension

For a rational Levi subgroup `M` of a connected reductive group `G` over `k` and a rational
Levi subgroup `M₁` of `G_K` mapping into `M_K`, the base change of a split component of `M`
factors through a split component of `M₁`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Split components under field extension.** For a rational Levi subgroup `M` of `G` over
`k` and a rational Levi subgroup `M₁` of `G_K` mapping into `M_K` compatibly with the inclusions
into `G_K`, the base change of a split component `A_M` factors through a split component
`A_{M₁}`. -/
def FieldLeviSplitComponentInclusionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    let f := algebraBaseMap k K
    let BC := GroupScheme.baseChange f
    ∀ (P M : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G) (l : M ⟶ P),
      IsParabolicSubgroup p → IsRationalLeviSubgroup l →
      ∀ (P₁ M₁ : GroupScheme (Spec (CommRingCat.of K))) (p₁ : P₁ ⟶ BC.obj G) (l₁ : M₁ ⟶ P₁),
        IsParabolicSubgroup p₁ → IsRationalLeviSubgroup l₁ →
        ∀ m : M₁ ⟶ BC.obj M, m ≫ BC.map (l ≫ p) = l₁ ≫ p₁ →
          ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M),
            IsSplitComponent a →
            ∀ (A₁ : CommGroupScheme (Spec (CommRingCat.of K))) (a₁ : A₁.toGrp ⟶ M₁),
              IsSplitComponent a₁ →
              ∃ j : (CommGroupScheme.baseChange f).obj A ⟶ A₁,
                CommGroupScheme.groupHom j ≫ a₁ ≫ m = BC.map a

end Langlands.GroupScheme
