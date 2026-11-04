import Langlands.GroupScheme.Lie.ElementCentralizer
import Langlands.GroupScheme.Lie.SemisimpleElement
import Langlands.GroupScheme.Reductive.Basic

/-! # Smoothness target for semisimple Lie-element centralizers -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Lie

/-- A closed representative of the actual stabilizer of a representation-tested
geometrically semisimple Lie element is smooth. -/
def SemisimpleCentralizerSmoothStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (X : lieKernel G k), IsSemisimpleElement G X →
    ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (j : C ⟶ G),
      (elementCentralizer G X).IsRepresentedBy j → IsClosedSubgroup j →
        Smooth C.X.hom

end Langlands.GroupScheme.Lie
