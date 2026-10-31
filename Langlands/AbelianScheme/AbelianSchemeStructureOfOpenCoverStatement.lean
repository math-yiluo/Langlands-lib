import Langlands.AbelianScheme.Basic

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

def AbelianSchemeStructureOfOpenCoverStatement : Prop :=
  ∀ (S : Scheme.{u}) (P : Over S) (s : 𝟙_ (Over S) ⟶ P)
    (𝒰 : S.OpenCover.{u}),
    (∀ i, ∃ B : AbelianScheme (𝒰.X i),
      Nonempty ((Over.pullback (𝒰.f i)).obj P ≅ B.X)) →
      ∃ (B : AbelianScheme S) (e : P ≅ B.X), s ≫ e.hom = η[B.X]

end Langlands.AbelianScheme
