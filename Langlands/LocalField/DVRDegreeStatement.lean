import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Inertia

/-! # The ramification-inertia lower degree bound for DVRs -/

namespace Langlands.LocalField

universe uR uS uK uL

/-- For a local extension of DVRs with compatible fraction fields of finite
degree, the ramification index times the inertia degree is at most that degree. -/
def DVRDegreeLowerBound : Prop :=
  ∀ (R : Type uR) (S : Type uS) (K : Type uK) (L : Type uL)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Field L]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    [Module.Finite K L],
    (IsLocalRing.maximalIdeal S).ramificationIdx R *
      (IsLocalRing.maximalIdeal S).inertiaDeg R ≤ Module.finrank K L

end Langlands.LocalField
