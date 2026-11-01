import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.FractionRing

universe u v w

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- Finite integral closure over a normal integer base, descent along a finite
normal subbase, and finite normalization in positive characteristic. -/
def NormalizationToolsStatement : Prop :=
  (∀ (R : Type u) (K : Type v) (L : Type w)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Algebra.FiniteType ℤ R] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    [FiniteDimensional K L],
      Module.Finite R (integralClosure R L)) ∧
  (∀ (B : Type v) (A : Type u)
    [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    [Algebra.FiniteType ℤ B] [CommRing A] [IsDomain A]
    [Algebra B A] [FaithfulSMul B A] [Module.Finite B A],
      Module.Finite A (integralClosure A (FractionRing A))) ∧
  (∀ (k : Type v) (A : Type u) [Field k] [Finite k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A],
      Module.Finite A (integralClosure A (FractionRing A))) ∧
  (∀ (A : Type u) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A]
    (p : ℕ) [Fact p.Prime] [CharP A p],
      Module.Finite A (integralClosure A (FractionRing A)))

end Langlands.AlgebraicGeometry.NoetherianApproximation
