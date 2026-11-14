import Langlands.GroupScheme.Torus.WeilRestrictionCommutative
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Etale.Basic

/-! # Statement: every torus is a quotient of an induced torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Tori are quotients of induced tori** (Milne, *Algebraic Groups* (2017),
Proposition 12.63). Let `T` be a torus over a field `k`. There are an étale `k`-algebra `A`
and a quotient map (a faithfully flat homomorphism) from the induced torus `(𝔾_m)_{A/k}`
onto `T`. -/
def InducedTorusQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] (T : GroupScheme (Spec (CommRingCat.of k))), IsTorus T →
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra k A) (_ : Algebra.Etale k A)
      (_ : Module.Finite k A) (q : WeilGm.groupScheme (CommRingCat.of k) A ⟶ T),
      Flat q.hom.hom.left ∧ Surjective q.hom.hom.left

end Langlands.GroupScheme
