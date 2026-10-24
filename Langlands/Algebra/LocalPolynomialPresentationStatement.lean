import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # A local polynomial presentation of an essentially finite type algebra -/

universe u v

namespace Langlands.Algebra

/-- The polynomial-localization presentation used at the start of the proof of
Stacks tag 05UV, extracted with the finite-type hypothesis of its statement.
This proposition states the presentation result; it does not prove it. -/
def LocalPolynomialPresentationStatement : Prop :=
  ∀ (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)],
    _root_.Algebra.EssFiniteType R S →
    ∃ (n : ℕ) (q : Ideal (MvPolynomial (Fin n) R)) (hq : q.IsPrime),
      letI := hq
      ∃ f : Localization.AtPrime q →ₐ[R] S,
        Function.Surjective f ∧
        IsLocalHom (algebraMap R (Localization.AtPrime q)) ∧
        IsLocalHom f.toRingHom

end Langlands.Algebra
