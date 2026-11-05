import Mathlib.Basic.NNReal.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Valuation.ValuationSubring

/-! # Galois-invariant real valuations over a Henselian valuation ring -/

universe u v

open scoped NNReal

namespace Langlands.FieldTheory

/-- A real-valued valuation with Henselian valuation subring has a normalized,
Galois-invariant prolongation to every algebraic Galois extension. -/
def HenselianRealGaloisProlongationStatement : Prop :=
  ∀ (K : Type u) [Field K] (ν : Valuation K ℝ≥0),
    HenselianLocalRing ν.valuationSubring →
    ∀ (Ω : Type v) [Field Ω] [Algebra K Ω] [IsGalois K Ω],
      ∃ w : Valuation Ω ℝ≥0,
        w.comap (algebraMap K Ω) = ν ∧
        ∀ (σ : Gal(Ω/K)) (x : Ω), w (σ x) = w x

end Langlands.FieldTheory
