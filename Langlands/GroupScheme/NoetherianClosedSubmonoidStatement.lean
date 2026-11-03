import Langlands.GroupScheme.RepresentabilityTransfer
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Closed submonoid recognition over an arbitrary base -/

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ImageGeneration

/-- An actual closed submonoid of a group scheme is a closed subgroup when
its square is Noetherian and affine. The representing scheme is identified
with the original submonoid by an actual isomorphism. -/
def NoetherianClosedSubmonoidStatement : Prop :=
  ∀ (B : Scheme.{u}) (G : GroupScheme B) (Z : Over B)
    (j : Z ⟶ G.X), IsClosedImmersion j.left →
    ∀ (m : Z ⊗ Z ⟶ Z),
      m ≫ j = (fst Z Z ≫ j) * (snd Z Z ≫ j) →
    ∀ (e : 𝟙_ (Over B) ⟶ Z), e ≫ j = 1 →
      IsAffine (Z ⊗ Z).left → IsLocallyNoetherian (Z ⊗ Z).left →
      ∃ (H : GroupScheme B) (i : H ⟶ G),
        IsClosedSubgroup i ∧
          ∃ a : Z ≅ H.X, a.hom ≫ i.hom.hom = j

end Langlands.GroupScheme.ImageGeneration
