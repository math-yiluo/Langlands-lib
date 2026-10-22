import Langlands.AbelianScheme.Tate.TwistPrimeComparison

namespace Langlands.TateTwist.Divisibility

universe u

/-- The canonical full comparison is a topological additive equivalence. -/
def FullPrimeProductComparison (R : Type u) [CommRing R] : Prop :=
  ∃ e : Full R ≃+ PrimeProduct R,
    e.toAddMonoidHom = toPrimeProduct R ∧
      Continuous e ∧ Continuous e.symm

/-- The canonical away comparison is a topological additive equivalence. -/
def AwayPrimeProductComparison (R : Type u) [CommRing R] (m : ℕ) : Prop :=
  ∃ e : Away R m ≃+ AwayPrimeProduct R m,
    e.toAddMonoidHom = toAwayPrimeProduct R m ∧
      Continuous e ∧ Continuous e.symm

/-- The full and all away comparisons, stated as one decomposition obligation. -/
def PrimeProductComparisons (R : Type u) [CommRing R] : Prop :=
  FullPrimeProductComparison R ∧ ∀ m : ℕ, AwayPrimeProductComparison R m

end Langlands.TateTwist.Divisibility
