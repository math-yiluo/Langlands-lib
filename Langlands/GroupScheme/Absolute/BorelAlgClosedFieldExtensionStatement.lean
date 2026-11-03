import Langlands.GroupScheme.Absolute.Borel

/-! # Borel subgroups under extensions of algebraically closed fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- An arbitrary extension between algebraically closed fields preserves an actual
Borel subgroup inclusion in a smooth connected affine group scheme. -/
def BorelAlgClosedFieldExtensionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsAffineHom G.X.hom → Smooth G.X.hom → ConnectedSpace G.X.left →
      ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G),
        IsBorelSubgroup i →
          IsBorelSubgroup
            ((GroupScheme.baseChange
              (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i)

end Langlands.GroupScheme
