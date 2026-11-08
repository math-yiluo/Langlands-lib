import Langlands.LocalFactor.Ramification.Herbrand.Finite
import Langlands.HarmonicAnalysis.Conductor
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs
import Mathlib.FieldTheory.Galois.Basic

/-!
# The first-order norm–trace congruence for large valuations

Proposition only; no proof is claimed.
-/

noncomputable section

universe u v w

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

/-- Deligne--Henniart 1981, Corollary 3.12(i), for a finite extension `L/K` of p-adic
fields inside a finite Galois extension `M/K`. Let `n ≥ 1` exceed `α(L/K)`: some upper
ramification group of `M/K` of index `w < n` fixes `L`. Then every nonzero `y ∈ L` with
`ψ_{L/K}(n) = φ_{M/L}(ψ_{M/K}(n)) ≤ ord_L y` has trace of order at least `n`, and the norm
of `1 + y` agrees with `1 + Tr y` up to a principal unit of level `n + 1` of `K`. -/
def TopLayerNormTraceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{u} p) (L : PadicField.{v} p)
    (M : PadicField.{w} p)
    [Algebra K.Carrier L.Carrier] [Algebra L.Carrier M.Carrier] [Algebra K.Carrier M.Carrier]
    [IsScalarTower K.Carrier L.Carrier M.Carrier]
    [IsScalarTower (Padic p) K.Carrier L.Carrier] [IsScalarTower (Padic p) L.Carrier M.Carrier]
    [IsScalarTower (Padic p) K.Carrier M.Carrier]
    [FiniteDimensional K.Carrier L.Carrier] [FiniteDimensional K.Carrier M.Carrier]
    [IsGalois K.Carrier M.Carrier]
    (TK : K.TopologicalData) (TL : L.TopologicalData) (TM : M.TopologicalData) (n : ℕ),
    1 ≤ n →
    (∃ w : ℝ, w < n ∧ ∀ σ ∈ Ramification.Padic.upperRamificationGroup TM K.Carrier w,
      ∀ x : L.Carrier, σ (algebraMap L.Carrier M.Carrier x) = algebraMap L.Carrier M.Carrier x) →
    ∀ y : L.Carrier, y ≠ 0 →
      Ramification.Padic.herbrandPhi TM L.Carrier
          (Ramification.Padic.herbrandPsi TM K.Carrier n) ≤ TL.ord y →
      Algebra.trace K.Carrier L.Carrier y ∈ TK.additiveLattice (-(n : ℤ)) ∧
      ∀ (z : L.Carrierˣ) (t : K.Carrierˣ), (z : L.Carrier) = 1 + y →
        (t : K.Carrier) = 1 + Algebra.trace K.Carrier L.Carrier y →
        Units.map (Algebra.norm K.Carrier) z * t⁻¹ ∈ TK.principalUnits (n + 1)

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
