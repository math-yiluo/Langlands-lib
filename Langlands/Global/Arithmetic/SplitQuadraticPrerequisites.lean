import Langlands.Global.Arithmetic.FieldRealizationStatement

/-! # Arithmetic prerequisites for split auxiliary quadratic fields -/

namespace Langlands.Global

universe u

/-- A signed rational can be a square over `ℚ_p` while remaining a nonsquare
in a prescribed number field. The Boolean `true` prescribes positive sign. -/
def PadicSquareNonsquareStatement : Prop :=
  ∀ (p : ℕ) (_ : Fact p.Prime) (K : Type u) (_ : Field K) (_ : NumberField K)
    (positive : Bool),
    ∃ d : ℚ, (if positive then 0 < d else d < 0) ∧
      IsSquare (algebraMap ℚ (Padic p) d) ∧ ¬ IsSquare (algebraMap ℚ K d)

/-- Two distinct rational algebra embeddings of a quadratic number field into
`ℚ_p` give exactly two actual finite primes and topological completion comparisons. -/
def QuadraticPadicSplittingStatement : Prop :=
  ∀ (p : ℕ) (_ : Fact p.Prime) (K : Type u) (_ : Field K) (_ : NumberField K),
    Module.finrank ℚ K = 2 →
    (∃ φ ψ : K →ₐ[ℚ] Padic p, φ ≠ ψ) → HasSplitQuadraticPrime p K

/-- The rational supply and actual local comparison used by the auxiliary
quadratic construction. -/
def SplitQuadraticPrerequisitesStatement : Prop :=
  PadicSquareNonsquareStatement.{u} ∧ QuadraticPadicSplittingStatement.{u}

end Langlands.Global
