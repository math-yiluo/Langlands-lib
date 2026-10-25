import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Noetherian.Basic

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

/-- The invariant subalgebra of a finite étale algebra over a noetherian base
is finite and étale over that base. -/
def InvariantAlgebraFiniteEtale (R A G : Type u)
    [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A]
    [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A] : Prop :=
  Module.Finite R (FixedPoints.subalgebra R A G) ∧
    Algebra.Etale R (FixedPoints.subalgebra R A G)

/-- Restriction to the invariant subalgebra is surjective on geometric points,
and its fibres are precisely the orbits under precomposition. -/
def InvariantAlgebraGeometricPoints (R A G Ω : Type u)
    [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A]
    [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
    [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] : Prop :=
  Function.Surjective (fun x : A →ₐ[R] Ω =>
    x.comp (FixedPoints.subalgebra R A G).val) ∧
  ∀ x y : A →ₐ[R] Ω,
    x.comp (FixedPoints.subalgebra R A G).val =
        y.comp (FixedPoints.subalgebra R A G).val ↔
      ∃ g : G, y = x.comp (MulSemiringAction.toAlgHom R A g)

/-- Elementwise surjectivity for invariants under localization: every invariant
localized element has an invariant numerator after clearing a power of `r`. -/
def InvariantAlgebraLocalization (R A B G : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (r : R) [IsLocalization.Away (algebraMap R A r) B]
    [Group G] [Finite G]
    [MulSemiringAction G A] [MulSemiringAction G B]
    [SMulCommClass G R A] [SMulCommClass G R B]
    (_hequiv : ∀ (g : G) (a : A), algebraMap A B (g • a) = g • algebraMap A B a) :
    Prop :=
  ∀ b : B, (∀ g : G, g • b = b) →
    ∃ a : A, (∀ g : G, g • a = a) ∧
      ∃ n : ℕ, algebraMap A B a = algebraMap R B (r ^ n) * b

end Langlands.AlgebraicGeometry.FiniteEtale
