import Langlands.Algebra.CocommutativeGradedGroupLike
import Langlands.Algebra.GroupLikeReconstruction

/-! # Reconstruction of graded cocommutative Hopf algebras -/

noncomputable section

universe u v w

namespace Langlands.GroupAlgebraCoaction

variable {K : Type u} [Field K] [IsAlgClosed K]
    {N : Type w} [AddCommGroup N]
    {A : Type v} [CommRing A] [HopfAlgebra K A] [Coalgebra.IsCocomm K A]

/-- Reconstruct a graded cocommutative Hopf algebra from its group-like elements,
    when the kernel map is surjective and degree zero is spanned by group-likes. -/
def groupAlgebraEquiv (π : A →ₐc[K] AddMonoidAlgebra K N)
    (hπ : Function.Surjective π)
    (h0 : grade π 0 ≤ Submodule.span K {x : A | IsGroupLikeElem K x}) :
    A ≃ₐc[K] AddMonoidAlgebra K (Additive (GroupLike K A)) :=
  (Langlands.MonoidAlgebra.bialgEquivOfSpanGroupLike
    (span_isGroupLikeElem_eq_top π hπ h0)).symm.trans
      (MonoidAlgebra.toAdditiveBialgEquiv K K (GroupLike K A))

end Langlands.GroupAlgebraCoaction
