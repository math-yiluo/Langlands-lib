import Langlands.GroupScheme.Lie.KernelTargetMaps
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Geometric smooth surjectivity from the actual differential -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

/-- An actual homomorphism between smooth affine groups over a field, with
connected target and surjective differential at the identity, is a smooth
surjection of schemes. -/
def SmoothSurjectiveOfSurjectiveDifferentialStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (H G : GroupScheme (Spec (CommRingCat.of k)))
    (_hH : Smooth H.X.hom) (_hG : Smooth G.X.hom)
    (hAffH : IsAffineHom H.X.hom) (hAffG : IsAffineHom G.X.hom)
    (_hConnG : ConnectedSpace G.X.left) (f : H ⟶ G),
    letI := hAffH
    letI := hAffG
    Function.Surjective (targetMapLinear f k) →
      Smooth f.hom.hom.left ∧ Surjective f.hom.hom.left

end Langlands.GroupScheme.Lie
