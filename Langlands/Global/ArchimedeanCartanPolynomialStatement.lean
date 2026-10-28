import Langlands.Global.ArchimedeanCasimirCartan
import Langlands.Global.ArchimedeanJointFinite
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Polynomial annihilation for the actual Cartan square sum -/

universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

/-- One monic polynomial in the actual Cartan square sum annihilates every
vector in a finite joint differential orbit, with degree its dimension. -/
def CartanSquareSumPolynomialAnnihilationStatement
    (K : Type u) [Field K] [NumberField K] (n : ℕ) : Prop :=
  ∀ f : SmoothFunctions K n, IsJointFinite K n f →
    ∃ p : Polynomial ℂ, p.Monic ∧
      p.natDegree = Module.finrank ℂ (jointOrbitSpan K n f) ∧
      ∀ g : SmoothFunctions K n, g ∈ jointOrbitSpan K n f →
        envelopingAction K n (Polynomial.aeval (cartanSquareSum K n) p) g = 0

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @CartanSquareSumPolynomialAnnihilationStatement

end Langlands.Global.ArchimedeanGL
