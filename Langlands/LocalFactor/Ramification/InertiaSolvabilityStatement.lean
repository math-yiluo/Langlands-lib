import Langlands.LocalField.Canonical
import Langlands.LocalFactor.Ramification.Galois
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Solvable

/-! # Solvability of actual finite p-adic inertia groups -/

namespace Langlands.Ramification.Padic

universe u v

/-- The actual inertia subgroup of every finite Galois extension of p-adic
fields is solvable. This is a proposition target, not a proof. -/
def FiniteInertiaSolvability : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{u} p) (L : PadicField.{v} p)
    [Algebra K.Carrier L.Carrier] [IsScalarTower (Padic p) K.Carrier L.Carrier]
    [IsGalois K.Carrier L.Carrier],
    Group.IsSolvable (inertia L.canonicalTopologicalData K.Carrier)

end Langlands.Ramification.Padic
