import Langlands.GroupScheme.Torus.WeilRestrictionCommutative
import Langlands.AlgebraicGeometry.PointTopology.UnirationalTransport
import Mathlib.RingTheory.Etale.Basic

/-! # Statement: rationality of Weil-restricted multiplicative groups and unirationality of tori -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

/-- **Unirationality of tori** (Milne, *Algebraic Groups* (2017), Proposition 12.60 and
Proposition 12.64). Let `k` be a field.
1. For every finite field extension `k'` of `k`, the Weil restriction `(𝔾_m)_{k'/k}` is
   rational: it is birational over `k` to a finite-dimensional affine space.
2. Every torus over `k` is unirational: there is a dominant morphism over `k` to it from a
   nonempty open subscheme of a finite-dimensional affine space.
3. Every induced torus `(𝔾_m)_{A/k}`, for `A` an étale `k`-algebra, is rational. -/
def TorusUnirationalityStatement : Prop :=
  ∀ (k : Type u) [Field k],
    (∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k'],
      HasFiniteAffineBirationalModel k (WeilGm.groupScheme (CommRingCat.of k) k').X) ∧
    (∀ T : GroupScheme (Spec (CommRingCat.of k)), IsTorus T → IsUnirational k T.X) ∧
    (∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.Etale k A] [Module.Finite k A],
      HasFiniteAffineBirationalModel k (WeilGm.groupScheme (CommRingCat.of k) A).X)

end Langlands.GroupScheme
