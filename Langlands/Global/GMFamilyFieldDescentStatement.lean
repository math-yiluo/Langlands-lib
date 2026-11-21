import Langlands.Global.GMFamilyFieldDescent

/-! # Arthur descent across a field extension

Arthur 2005, Lemma 17.5 and (17.13), with the actual nested Levi subgroups over a
field and an extension field, and the Euclidean normalizations of Arthur 1988, §7.
The admissible choice of Euclidean coordinates and the root and character comparisons
are conclusions, not supplied hypotheses about unrelated arrangements. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Classical

namespace Langlands.GMFamily

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

/-- **Arthur 2005, Lemma 17.5 (field-extension case).** If `M` is a rational Levi of
`G` and `M₁` is a rational Levi of `G_K` inside `M_K`, their actual split components
have compatible Euclidean coordinates giving the descent formula. The comparisons
include scalar extension of characters and the multiplicity-weighted root fibres. -/
def FieldExtensionDescentStatement : Prop :=
  ∀ (k K : Type u) [Field k] [CharZero k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    let f := algebraBaseMap k K
    let BC := GroupScheme.baseChange f
    ∀ (P M : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G) (l : M ⟶ P),
      IsParabolicSubgroup p → IsRationalLeviSubgroup l →
      ∀ (P₁ M₁ : GroupScheme (Spec (CommRingCat.of K))) (p₁ : P₁ ⟶ BC.obj G) (l₁ : M₁ ⟶ P₁),
        IsParabolicSubgroup p₁ → IsRationalLeviSubgroup l₁ →
        ∀ m : M₁ ⟶ BC.obj M, m ≫ BC.map (l ≫ p) = l₁ ≫ p₁ →
          ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M)
            (hA : IsSplitComponent a)
            (A₁ : CommGroupScheme (Spec (CommRingCat.of K))) (a₁ : A₁.toGrp ⟶ M₁)
            (hA₁ : IsSplitComponent a₁),
            HasActualFieldDescent (l ≫ p) (l₁ ≫ p₁) m a hA a₁ hA₁

end Langlands.GMFamily
