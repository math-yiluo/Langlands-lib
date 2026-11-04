import Langlands.GroupScheme.Lie.ElementCentralizer
import Langlands.GroupScheme.Lie.SemisimpleElement
import Langlands.GroupScheme.Reductive.Basic

/-! # Spanning target for centralizers of noncentral semisimple Lie elements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Lie

local instance {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom := by
  change IsAffineHom (Limits.pullback.snd G.X.hom (toAlgebraicClosure k))
  infer_instance

/-- If a smooth connected affine group over an infinite field has a geometric
noncentral semisimple Lie element, then it has one over the ground field,
and the actual tangent centralizers of all such elements span its Lie module. -/
def SemisimpleCentralizerSpanningStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    (∃ X : lieKernel ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G)
        (AlgebraicClosure k),
      IsSemisimpleElement ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G) X ∧
      elementCentralizerLie ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G) X ≠ ⊤) →
    (∃ X : lieKernel G k,
      IsSemisimpleElement G X ∧ elementCentralizerLie G X ≠ ⊤) ∧
    (⨆ (X : lieKernel G k) (_ : IsSemisimpleElement G X)
        (_ : elementCentralizerLie G X ≠ ⊤), elementCentralizerLie G X) = ⊤

end Langlands.GroupScheme.Lie
