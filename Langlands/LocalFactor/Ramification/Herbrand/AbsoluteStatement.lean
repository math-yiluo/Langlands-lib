import Langlands.LocalFactor.Ramification.Herbrand.Absolute
import Langlands.Galois.Local.AbsoluteDefinitions
import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Absolute upper ramification: arithmetic and continuity statements

These proposition definitions concern the published absolute filtration and
actual finite restrictions. They are targets for later proofs.
-/

noncomputable section

namespace Langlands.Ramification.Padic

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- Exact image in every actual finite Galois quotient, on Serre's domain. -/
def AbsoluteUpperFiniteImage : Prop :=
  ∀ (L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (v : ℝ), -1 ≤ v →
      (absoluteUpperRamificationGroup F v).map (absoluteFiniteRestriction F L).toMonoidHom =
        canonicalUpperRamificationGroup (absoluteFiniteExtension F L) F.Carrier v

/-- Comparison with the existing spectral-closure inertia for any legitimate
local-field realization of the base. -/
def AbsoluteUpperInertia (T : F.TopologicalData) : Prop :=
  absoluteUpperRamificationGroup F 0 = F.absoluteInertia T

/-- Explicit canonical specialization, available for every p-adic field. -/
def AbsoluteUpperCanonicalInertia : Prop :=
  absoluteUpperRamificationGroup F 0 = F.absoluteInertia F.canonicalTopologicalData

/-- The full-group boundary at the left endpoint of Serre's domain. -/
def AbsoluteUpperEndpoint : Prop :=
  absoluteUpperRamificationGroup F (-1) = ⊤

/-- Left continuity within Serre's domain; the endpoint is stated separately. -/
def AbsoluteUpperLeftContinuity : Prop :=
  ∀ v : ℝ, -1 < v →
    absoluteUpperRamificationGroup F v =
      ⨅ (w : ℝ) (_ : -1 ≤ w ∧ w < v), absoluteUpperRamificationGroup F w

/-- The closed right limit has the expected image in every finite quotient.
Closure uses the actual absolute Krull topology; finite targets are discrete. -/
def AbsoluteUpperClosedRightImage : Prop :=
  ∀ (L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (v : ℝ), -1 ≤ v →
      ((⨆ (w : ℝ) (_ : v < w),
        absoluteUpperRamificationGroup F w).topologicalClosure).map
          (absoluteFiniteRestriction F L).toMonoidHom =
        ⨆ (w : ℝ) (_ : v < w),
          canonicalUpperRamificationGroup (absoluteFiniteExtension F L) F.Carrier w

/-- The closed positive upper limit equals the finite-quotient description of
wild inertia, using the first lower group in every finite extension. -/
def AbsoluteUpperWildInertia : Prop :=
  (⨆ (w : ℝ) (_ : 0 < w), absoluteUpperRamificationGroup F w).topologicalClosure =
    ⨅ L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier),
      (lowerRamificationGroup (absoluteFiniteExtension F L).canonicalTopologicalData
        F.Carrier 1).comap (absoluteFiniteRestriction F L).toMonoidHom

/-- The complete family for all primes, all finite p-adic fields in universe
`u`, all legitimate base realizations, all finite subextensions and real indices. -/
def AbsoluteHerbrandArithmetic : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p),
    AbsoluteUpperFiniteImage F ∧
    (∀ T : F.TopologicalData, AbsoluteUpperInertia F T) ∧
    AbsoluteUpperCanonicalInertia F ∧
    AbsoluteUpperEndpoint F ∧
    AbsoluteUpperLeftContinuity F ∧
    AbsoluteUpperClosedRightImage F ∧
    AbsoluteUpperWildInertia F

end Langlands.Ramification.Padic
