import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Reductive.UnipotentRadical
import Langlands.GroupScheme.Rational.Characters
import Mathlib.GroupTheory.PGroup

/-! # Maximal p-subgroups of reductive groups over finite fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over a finite field of characteristic `p`, maximal `p`-subgroups of the
actual rational-point group are exactly the rational-point images of
unipotent radicals of field-defined geometric Borel subgroups. -/
def FiniteFieldSylowBorelStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k]
    (G : GroupScheme (Spec (CommRingCat.of k))), IsConnectedReductive G →
    ∀ H : Subgroup (rationalPoints G),
      (IsPGroup (ringChar k) H ∧
        ∀ H' : Subgroup (rationalPoints G),
          H ≤ H' → IsPGroup (ringChar k) H' → H' = H) ↔
      ∃ (B U : GroupScheme (Spec (CommRingCat.of k)))
        (i : B ⟶ G) (j : U ⟶ B),
        IsGeometricBorelSubgroup i ∧ IsUnipotentRadical j ∧
          H = (rationalPoints.map (j ≫ i)).range

end Langlands.GroupScheme
