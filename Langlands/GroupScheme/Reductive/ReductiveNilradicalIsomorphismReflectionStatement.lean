import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.LatticeGalois
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! # Statement: reductive isomorphisms and the nilradical quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Isomorphism of two reductive groups over a local ring is reflected by
pullback to the quotient by its nilradical. -/
def ReductiveNilradicalIsomorphismReflectionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (G H : GroupScheme (Spec (CommRingCat.of R)))
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom],
    IsReductive G → IsReductive H →
      Nonempty
        (((GroupScheme.baseChange (algebraBaseMap R (R ⧸ nilradical R))).obj G) ≅
          ((GroupScheme.baseChange (algebraBaseMap R (R ⧸ nilradical R))).obj H)) →
      Nonempty (G ≅ H)

end Langlands.GroupScheme
