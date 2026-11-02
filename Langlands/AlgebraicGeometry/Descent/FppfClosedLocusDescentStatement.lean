import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Sites.Closed

/-! # fppf descent of closed loci

A sieve on a scheme that is closed for the fppf topology, and that is cut out by a closed
immersion on the members of an fppf covering sieve, is cut out by one closed immersion.
This is the subfunctor form of effective fpqc descent of closed immersions (Stacks Project,
Descent, Lemma 35.37.2, Tag 03I0), specialized to fppf coverings.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Let `E` be a sieve on a scheme `Y` that is closed for the fppf topology. Suppose that
some fppf covering sieve `R` of `Y` has the following property: for every member
`f : Y' ⟶ Y` of `R` there is a closed immersion `ι : Z ⟶ Y'` such that a morphism
`g : T ⟶ Y'` factors through `ι` exactly when `g ≫ f` belongs to `E`. Then there is a
closed immersion `ι : Z ⟶ Y` such that a morphism `g : T ⟶ Y` factors through `ι` exactly
when `g` belongs to `E`. -/
def FppfClosedLocusDescentStatement : Prop :=
  ∀ (Y : Scheme.{u}) (E : Sieve Y), Scheme.fppfTopology.IsClosed E →
    (∃ R ∈ Scheme.fppfTopology Y, ∀ ⦃Y' : Scheme.{u}⦄ (f : Y' ⟶ Y), R f →
      ∃ (Z : Scheme.{u}) (ι : Z ⟶ Y'), IsClosedImmersion ι ∧
        ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ Y'), (∃ k : T ⟶ Z, k ≫ ι = g) ↔ E (g ≫ f)) →
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ Y), IsClosedImmersion ι ∧
      ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ Y), (∃ k : T ⟶ Z, k ≫ ι = g) ↔ E g

end Langlands.AlgebraicGeometry
