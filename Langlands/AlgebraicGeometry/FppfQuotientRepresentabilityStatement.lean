import Langlands.AlgebraicGeometry.HQuasiProjective
import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Representability of an fppf sheaf by a quasi-projective scheme through a flat proper
equivalence relation -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

open AlgebraicSpace

/-- Let `A` be a noetherian ring, `S = Spec A`, `G` an fppf sheaf on schemes over `S`, `Z` an
H-quasi-projective scheme over `S` and `ζ : Z ⟶ G` an fppf-locally surjective morphism of
presheaves. Let `s t : R ⟶ Z` be morphisms over `S` such that `R` with `s` and `t` is the fibre
product `Z ×_G Z` in presheaves. If `s` is flat and proper, then `G` is represented by an
H-quasi-projective scheme `Q` over `S`, through an isomorphism under which `ζ` becomes a flat,
surjective, proper morphism `π : Z ⟶ Q` over `S`, locally of finite presentation. -/
def FppfQuotientRepresentabilityStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A]
    (G : FppfSheaf (Spec (CommRingCat.of A))) (Z R : Over (Spec (CommRingCat.of A)))
    (ζ : (schemeYoneda _).obj Z ⟶ G.obj) (s t : R ⟶ Z),
    IsHQuasiProjective Z.hom →
    Presheaf.IsLocallySurjective (fppfTopology _) ζ →
    IsPullback ((schemeYoneda _).map s) ((schemeYoneda _).map t) ζ ζ →
    Flat s.left → IsProper s.left →
      ∃ (Q : Over (Spec (CommRingCat.of A))) (π : Z ⟶ Q)
        (e : (schemeYoneda _).obj Q ≅ G.obj),
        IsHQuasiProjective Q.hom ∧ (schemeYoneda _).map π ≫ e.hom = ζ ∧
          Flat π.left ∧ Surjective π.left ∧ IsProper π.left ∧
            LocallyOfFinitePresentation π.left

end Langlands.AlgebraicGeometry
