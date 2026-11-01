import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.RingTheory.Filtration

universe u v

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- Two algebraic tools for lifting normalization from a closed fibre. -/
def ClosedFiberNormalizationToolsStatement : Prop :=
  (∀ {R : Type u} {S : Type v} [CommRing R] [IsDomain R] [IsNoetherianRing R]
      [CommRing S] [IsDomain S] (f : R →+* S) (r : R),
      ¬ IsUnit r → f r ≠ 0 → RingHom.ker f ≤ Ideal.span {r} →
        Function.Injective f) ∧
  (∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime] (J : Ideal S)
      [Module.Finite R (S ⧸ J)],
      J ≤ (q.under R).map (algebraMap R S) → Algebra.QuasiFiniteAt R q)

end Langlands.AlgebraicGeometry.NoetherianApproximation
