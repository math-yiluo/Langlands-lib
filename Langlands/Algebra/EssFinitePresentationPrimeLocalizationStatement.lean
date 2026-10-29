import Langlands.Algebra.EssFinitePresentation
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Prime-localization presentation of an essentially finitely presented local algebra -/

universe u v

namespace Langlands.Algebra

/-- The presentation used in the first line of the proof of Stacks Lemma 10.127.11 (tag 00QV):
an essentially finitely presented `R`-algebra `S` that is a local ring is, as an `R`-algebra,
the localization of a finitely presented quotient `R[x₁, …, xₙ]/I` at a prime ideal.
No locality hypothesis on `R` or on `R → S` is imposed. This proposition states the
conversion; it does not prove it. -/
def EssFinitePresentationPrimeLocalizationStatement : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] [IsLocalRing S] [Algebra R S],
    EssFinitePresentation R S →
    ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) R)) (_ : I.FG)
      (q : Ideal (MvPolynomial (Fin n) R ⧸ I)) (hq : q.IsPrime),
      letI := hq
      Nonempty (Localization.AtPrime q ≃ₐ[R] S)

end Langlands.Algebra
