import Langlands.AlgebraicGeometry.HQuasiProjective
import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Representability of an fppf sheaf on locally noetherian tests through a flat proper
equivalence relation -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry

open AlgebraicSpace

/-- Let `A` be a noetherian ring, `S = Spec A`, `G` an fppf sheaf on schemes over `S`, `Z` an
H-quasi-projective scheme over `S` and `ζ : Z ⟶ G` an fppf-locally surjective morphism of
presheaves. Let `s t : R ⟶ Z` be morphisms over `S` with `ζ ∘ s = ζ ∘ t` such that, for every
locally noetherian `T` over `S`, two `T`-points of `Z` with the same image in `G` come from a
unique `T`-point of `R`. If `s` is flat and proper, then there are an H-quasi-projective
scheme `Q` over `S`, a flat, surjective, proper morphism `π : Z ⟶ Q` over `S`, locally of finite
presentation, and a morphism `e` from the functor of points of `Q` to `G` with `e ∘ π = ζ`
that is bijective on the points of every locally noetherian scheme over `S`. -/
def FppfQuotientLocallyNoetherianStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A]
    (G : FppfSheaf (Spec (CommRingCat.of A))) (Z R : Over (Spec (CommRingCat.of A)))
    (ζ : (schemeYoneda _).obj Z ⟶ G.obj) (s t : R ⟶ Z),
    IsHQuasiProjective Z.hom →
    Presheaf.IsLocallySurjective (fppfTopology _) ζ →
    (schemeYoneda _).map s ≫ ζ = (schemeYoneda _).map t ≫ ζ →
    (∀ (T : Over (Spec (CommRingCat.of A))) [IsLocallyNoetherian T.left] (x y : T ⟶ Z),
        ζ.app (op T) (ULift.up x) = ζ.app (op T) (ULift.up y) →
          ∃! r : T ⟶ R, r ≫ s = x ∧ r ≫ t = y) →
    Flat s.left → IsProper s.left →
      ∃ (Q : Over (Spec (CommRingCat.of A))) (π : Z ⟶ Q)
        (e : (schemeYoneda _).obj Q ⟶ G.obj),
        IsHQuasiProjective Q.hom ∧ (schemeYoneda _).map π ≫ e = ζ ∧
          (∀ (T : Over (Spec (CommRingCat.of A))) [IsLocallyNoetherian T.left],
            Function.Bijective (e.app (op T))) ∧
          Flat π.left ∧ Surjective π.left ∧ IsProper π.left ∧
            LocallyOfFinitePresentation π.left

end Langlands.AlgebraicGeometry
