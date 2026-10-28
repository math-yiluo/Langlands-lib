import Langlands.Global.ArchimedeanJointFinite
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Polynomial annihilation on a finite joint differential orbit -/

universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

/-- A sum of actual central and compact differential operators has a monic
annihilator on each finite joint orbit, of degree equal to its dimension. -/
def JointOrbitPolynomialAnnihilationStatement
    (K : Type u) [Field K] [NumberField K] (n : ℕ) : Prop :=
  ∀ f : SmoothFunctions K n, IsJointFinite K n f →
    ∀ (z : EnvelopingCenter K n) (b : compactEnvelopingSubalgebra K n),
      ∃ p : Polynomial ℂ, p.Monic ∧
        p.natDegree = Module.finrank ℂ (jointOrbitSpan K n f) ∧
        ∀ g : SmoothFunctions K n, g ∈ jointOrbitSpan K n f →
          envelopingAction K n
            (Polynomial.aeval (centerInclusion K n z + b.val) p) g = 0

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @JointOrbitPolynomialAnnihilationStatement

end Langlands.Global.ArchimedeanGL
