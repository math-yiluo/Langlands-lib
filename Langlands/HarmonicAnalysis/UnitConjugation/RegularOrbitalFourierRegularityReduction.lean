import Langlands.HarmonicAnalysis.UnitConjugation.EllipticRegularOrbitalFourierRegularityStatement
import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer
import Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalFourierDescentStatement
import Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalFourierRegularityStatement

/-!
# Harish-Chandra's Theorem 1.1 from its elliptic case and parabolic descent

Harish-Chandra proves the local summability in Theorem 1.1 by induction on `dim G`: if the
Cartan subalgebra containing the regular element is not elliptic, parabolic descent to a proper
Levi subgroup and the induction hypothesis give the result (§1.4); the elliptic case is proved
directly (§§1.5–1.6). This module carries out the induction for the Lie algebra `A` of the unit
group of a finite-dimensional semisimple algebra over a nonarchimedean local field of
characteristic zero: `regularOrbitalFourierRegularityReduction` proves
`RegularOrbitalFourierRegularityReductionStatement`, the implication from
`EllipticRegularOrbitalFourierRegularityStatement` (the elliptic case) and
`RegularOrbitalFourierDescentStatement` (descent to the centralizer of an idempotent) to
`RegularOrbitalFourierRegularityStatement`. It does not prove the two inputs.

The induction is on `dim_F A`. A regular `X` that is not elliptic commutes with a non-central
idempotent `e` (`not_isEllipticElement_iff`); the centralizer `M` of `e` is a semisimple
algebra (`IdempotentCentralizer.isSemisimpleRing_centralizer`) of smaller dimension
(`IdempotentCentralizer.finrank_centralizer_lt`) in which `X` is regular
(`IdempotentCentralizer.mem_regularSet_centralizer`); the induction hypothesis gives the
conclusion at `X` for `M`, and descent gives it for `A`.

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), §1, printed pp. 5 and 10–11: "We shall prove this theorem by
induction on `dim G`", and the reduction to the elliptic case in §1.4.
-/

namespace Langlands.HarmonicAnalysis

open MeasureTheory UnitConjugation QuotientIntegration Module

universe u v

/-- Harish-Chandra's derivation of Theorem 1.1 (local summability) from its elliptic case and
parabolic descent, for the unit groups of finite-dimensional semisimple algebras: the elliptic
case and descent to the centralizers of idempotents imply the local summability of the Fourier
transforms of all regular orbital distributions. -/
def RegularOrbitalFourierRegularityReductionStatement.{u', v'} : Prop :=
  EllipticRegularOrbitalFourierRegularityStatement.{u', v'} →
    RegularOrbitalFourierDescentStatement.{u', v'} →
      RegularOrbitalFourierRegularityStatement.{u', v'}

namespace RegularOrbitalFourierRegularityReduction

/-- `RegularOrbitalFourierRegularityStatement` is the conclusion `OrbitalFourierRegularityAt`
at every regular element of every finite-dimensional semisimple algebra. -/
theorem regularOrbitalFourierRegularityStatement_of_forall
    (h : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] [CharZero F] (A : Type v) [Ring A] [Algebra F A]
      [FiniteDimensional F A] [IsSemisimpleRing A], ∀ X ∈ regularSet F A,
        OrbitalFourierRegularityAt F A X) :
    RegularOrbitalFourierRegularityStatement.{u, v} :=
  fun F _ _ _ _ _ A _ _ _ _ _ _ _ _ _ _ ψ B hB μ X hX => h F A X hX ψ B hB μ

/-- The elliptic case, in the form `OrbitalFourierRegularityAt`. -/
theorem orbitalFourierRegularityAt_of_isEllipticElement
    (hE : EllipticRegularOrbitalFourierRegularityStatement.{u, v})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (A : Type v) [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
    (X : A) (hX : X ∈ regularSet F A) (hEll : IsEllipticElement X) :
    OrbitalFourierRegularityAt F A X :=
  fun ψ B hB μ => hE F A ψ B hB μ X hX hEll

/-- The induction on the dimension: from the elliptic case and descent, the conclusion holds at
every regular element of every finite-dimensional semisimple algebra of dimension `n`. -/
theorem orbitalFourierRegularityAt_of_finrank_eq
    (hE : EllipticRegularOrbitalFourierRegularityStatement.{u, v})
    (hD : RegularOrbitalFourierDescentStatement.{u, v})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (n : ℕ) :
    ∀ (A : Type v) [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A],
      finrank F A = n → ∀ X ∈ regularSet F A, OrbitalFourierRegularityAt F A X := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A _ _ _ _ hn X hX
    by_cases hEll : IsEllipticElement X
    · exact orbitalFourierRegularityAt_of_isEllipticElement hE F A X hX hEll
    · obtain ⟨e, he, hcomm, hnc⟩ := (not_isEllipticElement_iff X).1 hEll
      have hXM : X ∈ Subalgebra.centralizer F ({e} : Set A) :=
        (IdempotentCentralizer.mem_centralizer_singleton_iff F).2 hcomm
      have : IsSemisimpleRing (Subalgebra.centralizer F ({e} : Set A)) :=
        IdempotentCentralizer.isSemisimpleRing_centralizer F he
      have : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
      have hlt : finrank F (Subalgebra.centralizer F ({e} : Set A)) < n :=
        hn ▸ IdempotentCentralizer.finrank_centralizer_lt F hnc
      have hreg := IdempotentCentralizer.mem_regularSet_centralizer he ⟨X, hXM⟩ hX
      exact hD F A e he ⟨X, hXM⟩ hX (ih _ hlt _ rfl _ hreg)

/-- **Harish-Chandra's Theorem 1.1 (local summability) from its elliptic case and parabolic
descent.** -/
theorem regularOrbitalFourierRegularityReduction :
    RegularOrbitalFourierRegularityReductionStatement.{u, v} := fun hE hD =>
  regularOrbitalFourierRegularityStatement_of_forall fun F _ _ _ _ _ A _ _ _ _ X hX =>
    orbitalFourierRegularityAt_of_finrank_eq hE hD F _ A rfl X hX

end RegularOrbitalFourierRegularityReduction

end Langlands.HarmonicAnalysis
