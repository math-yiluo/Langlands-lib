import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Propagation of flatness by group translations -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For a finite surjective group endomorphism over an algebraically closed
field, flatness over a nonempty target open implies flatness everywhere.
This is a proposition definition, not a proof. -/
def TranslationFlatStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (G : Grp (Over (Spec (CommRingCat.of K)))) (f : G ⟶ G),
    LocallyOfFiniteType G.X.hom → IsFinite f.hom.hom.left →
      Surjective f.hom.hom.left →
      (∃ U : G.X.left.Opens,
        Set.Nonempty (U : Set G.X.left) ∧ Flat (f.hom.hom.left ∣_ U)) →
      Flat f.hom.hom.left

end Langlands.GroupScheme
