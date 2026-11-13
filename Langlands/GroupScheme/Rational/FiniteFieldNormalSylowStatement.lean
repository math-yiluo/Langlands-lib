import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.Rational.Characters
import Mathlib.GroupTheory.PGroup

/-! # Normal Sylow subgroups in the defining characteristic -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- If the rational-point group of a connected reductive group over a finite
field has a normal maximal subgroup among the defining-characteristic
`p`-subgroups, then the algebraic group is a torus. -/
def FiniteFieldNormalSylowTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k]
    (G : GroupScheme (Spec (CommRingCat.of k))), IsConnectedReductive G →
    ∀ H : Subgroup (rationalPoints G),
      IsPGroup (ringChar k) H →
      (∀ H' : Subgroup (rationalPoints G),
        H ≤ H' → IsPGroup (ringChar k) H' → H' = H) →
      H.Normal → IsTorus G

end Langlands.GroupScheme
