import Langlands.LocalFactor.Ramification.Herbrand.GeneralAbsolute
import Langlands.Galois.Local.AbsoluteDefinitions
import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Absolute upper ramification in any characteristic: statements

Proposition definitions for the upper filtration of a separable closure `Ω` of a
nonarchimedean local field `K` of either characteristic, as published by
`Herbrand.GeneralAbsolute`, and for its finite restrictions. Finite subextensions are
the `FiniteGaloisIntermediateField K Ω`, with their canonical finite-level structures
`localTopologicalData K L`. These are targets for later proofs, not assumptions.
-/

noncomputable section

namespace Langlands.Ramification.Local

universe uK uΩ

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- Exact image in every finite Galois quotient, on Serre's domain `-1 ≤ v`. -/
def AbsoluteUpperFiniteImage : Prop :=
  ∀ (L : FiniteGaloisIntermediateField K Ω) (v : ℝ), -1 ≤ v →
    (localAbsoluteUpperRamificationGroup K Ω v).map
        (absoluteFiniteRestriction K Ω L).toMonoidHom =
      localUpperRamificationGroup K L v

/-- The member at `0` of the absolute upper filtration is the inertia subgroup,
the kernel of the residue projection of `Ω ≃ₐ[K] Ω`. -/
def AbsoluteUpperInertia : Prop :=
  localAbsoluteUpperRamificationGroup K Ω 0 = LocalGalois.SepClosed.absoluteInertia K Ω

/-- Left continuity within Serre's domain; the endpoint `-1` is excluded. -/
def AbsoluteUpperLeftContinuity : Prop :=
  ∀ v : ℝ, -1 < v →
    localAbsoluteUpperRamificationGroup K Ω v =
      ⨅ (w : ℝ) (_ : -1 ≤ w ∧ w < v), localAbsoluteUpperRamificationGroup K Ω w

/-- The closed right limit has the expected image in every finite quotient.
Closure uses the Krull topology; finite targets are discrete. -/
def AbsoluteUpperClosedRightImage : Prop :=
  ∀ (L : FiniteGaloisIntermediateField K Ω) (v : ℝ), -1 ≤ v →
    ((⨆ (w : ℝ) (_ : v < w),
      localAbsoluteUpperRamificationGroup K Ω w).topologicalClosure).map
        (absoluteFiniteRestriction K Ω L).toMonoidHom =
      ⨆ (w : ℝ) (_ : v < w), localUpperRamificationGroup K L w

/-- Wild inertia, the closed positive upper limit, is the subgroup of automorphisms
whose restriction to every finite Galois subextension lies in its first lower group. -/
def AbsoluteUpperWildInertia : Prop :=
  localWildInertia K Ω =
    ⨅ L : FiniteGaloisIntermediateField K Ω,
      (lowerRamificationGroup (localTopologicalData K L) K 1).comap
        (absoluteFiniteRestriction K Ω L).toMonoidHom

/-- The five statements for every nonarchimedean local field `K` and every
separable closure `Ω` of `K`, in independent universes. -/
def AbsoluteHerbrandArithmetic : Prop :=
  ∀ (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω],
    AbsoluteUpperFiniteImage K Ω ∧
    AbsoluteUpperInertia K Ω ∧
    AbsoluteUpperLeftContinuity K Ω ∧
    AbsoluteUpperClosedRightImage K Ω ∧
    AbsoluteUpperWildInertia K Ω

end Langlands.Ramification.Local
