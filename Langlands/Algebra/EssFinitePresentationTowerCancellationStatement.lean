import Langlands.Algebra.EssFinitePresentation

/-! # Cancellation of essential finite presentation in an algebra tower -/

universe u v w

namespace Langlands.Algebra

/-- Derived cancellation for essential finite presentation: if `S` and `T` are
essentially finitely presented over `R` in a compatible algebra tower, then `T`
is essentially finitely presented over `S`. This defines the statement only. -/
def EssFinitePresentationTowerCancellationStatement : Prop :=
  ∀ (R : Type u) (S : Type v) (T : Type w)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T],
    EssFinitePresentation R S → EssFinitePresentation R T → EssFinitePresentation S T

end Langlands.Algebra
