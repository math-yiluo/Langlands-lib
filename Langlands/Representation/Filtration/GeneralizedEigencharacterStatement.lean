import Langlands.Representation.Filtration.Definitions
import Langlands.Representation.Exponents.Jacquet

/-!
# Generalized eigencharacters detected by actual graded quotients

The finite uniform power is retained after restricting the action along an
arbitrary monoid homomorphism. The filtration is supplied actual data.
-/

open CategoryTheory

namespace Langlands

universe uR uG uH uV uC vC

/-- A nonzero uniform character space in a finite filtered representation has
a nonzero image, with the same power, in one actual graded quotient. -/
def GeneralizedEigencharacterFiltrationStatement : Prop :=
  ∀ (R : Type uR) [CommRing R]
    (G : Type uG) [Monoid G] (H : Type uH) [Monoid H]
    (C : Type uC) [Category.{vC} C] (F : C ⥤ Rep.{uV} R G)
    (n : ℕ) (s : RepFunctorFiltration F n) (X : C)
    (ι : H →* G) (χ : H →* Rˣ) (k : ℕ),
    characterSpace ((F.obj X).ρ.comp ι) χ k ≠ ⊥ →
      ∃ i : Fin n,
        characterSpace (((s.graded i).obj X).ρ.comp ι) χ k ≠ ⊥

end Langlands
