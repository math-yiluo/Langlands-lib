import Langlands.Geometry.Building.SimplyConnectedNormalizerAffineWeylStatement
import Langlands.Geometry.Building.AffineIwahoriTitsNormalizerReduction
import Langlands.Geometry.Building.AffineIwahoriTitsProof

/-! # The action of `N(F) ∩ G(F)^♮` on the apartment has image `W(Ψ)`: proof -/

universe u

namespace Langlands.Geometry.Building

/-- **`N(F) ∩ G(F)^♮` acts through exactly `W(Ψ)`** (Kaletha–Prasad, Theorem 7.5.3(2), image
part). For parahoric building data satisfying the apartment axioms, the image of
`N(F) ∩ G(F)^♮` in the affine automorphisms of the apartment is the affine Weyl group of the
affine roots. -/
theorem simplyConnectedNormalizerAffineWeyl : SimplyConnectedNormalizerAffineWeylStatement.{u} :=
  simplyConnectedNormalizerAffineWeyl_of_affineIwahoriTits affineIwahoriTits

end Langlands.Geometry.Building
