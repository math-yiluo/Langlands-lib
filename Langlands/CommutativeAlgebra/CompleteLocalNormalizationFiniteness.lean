import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.FiniteType

/-! # Universal Japanese finiteness over a complete local ring -/

universe u

namespace Langlands.CommutativeAlgebra

/-- Universal Japanese finiteness for Noetherian local rings complete at
their maximal ideal, with the definitions unfolded into Mathlib vocabulary. -/
def CompleteLocalNormalizationFinitenessStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Algebra.FiniteType R S]
    (L : Type u) [Field L] [Algebra (FractionRing S) L] [Algebra S L]
    [IsScalarTower S (FractionRing S) L] [FiniteDimensional (FractionRing S) L],
    Module.Finite S (integralClosure S L)

end Langlands.CommutativeAlgebra
