import Langlands.GroupScheme.Lie.ElementCentralizer
import Langlands.GroupScheme.Lie.SemisimpleElement
import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: central semisimple Lie elements and their centralizers -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Lie

/-- Milne, Corollary 17.77. Let `G` be a smooth connected affine group over a field `k` and
let `X` be a semisimple element of its Lie algebra (`IsSemisimpleElement`). Then `X` is
central, that is, its tangent centralizer `elementCentralizerLie G X = z_𝔤(X)` is all of
`Lie(G)`, if and only if its all-test centralizer `C_G(X)` is all of `G`. -/
def SemisimpleCentralElementStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (X : lieKernel G k), IsSemisimpleElement G X →
      (elementCentralizerLie G X = ⊤ ↔ elementCentralizer G X = ⊤)

end Langlands.GroupScheme.Lie
