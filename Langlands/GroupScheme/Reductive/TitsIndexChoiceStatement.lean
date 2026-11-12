import Langlands.GroupScheme.Reductive.TitsIndex

/-! # Existence and choice independence of actual Tits indices: statements -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every actual semisimple field group admits compatible choices defining
its Tits index. No existence conclusion is assumed in the hypotheses. -/
def TitsIndexExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom],
    IsSemisimple G → Nonempty (TitsIndexData G)

/-- All compatible choices for the same actual group give equivalent diagrams
with zero-restriction vertices and the full absolute Galois star action. -/
def TitsIndexIndependenceStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d e : TitsIndexData G),
    Nonempty (TitsIndexEquiv d e)

/-- The two choice assertions, retained as unproved proposition definitions. -/
def TitsIndexChoiceStatement : Prop :=
  TitsIndexExistenceStatement.{u} ∧ TitsIndexIndependenceStatement.{u}

end Langlands.GroupScheme
