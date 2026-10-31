import Langlands.Algebra.UniversalEnvelopingFiltration
import Langlands.Global.ArchimedeanLieAlgebra
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Finite degree pieces of the actual archimedean enveloping algebra -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] (n : ℕ)

/-- Constants and actual complexified archimedean matrix Lie generators. -/
abbrev envelopingDegreeOne : Submodule ℂ (EnvelopingAlgebra K n) :=
  Langlands.Algebra.UniversalEnveloping.degreeOne ℂ (ComplexLieAlgebra K n)

/-- The degree filtration on the genuine archimedean universal enveloping algebra. -/
abbrev envelopingDegreeFiltration (d : ℕ) : Submodule ℂ (EnvelopingAlgebra K n) :=
  Langlands.Algebra.UniversalEnveloping.degreeFiltration ℂ (ComplexLieAlgebra K n) d

/-- The strict degree pieces for the actual archimedean enveloping algebra. -/
abbrev envelopingDegreeFiltrationLT (d : ℕ) : Submodule ℂ (EnvelopingAlgebra K n) :=
  Langlands.Algebra.UniversalEnveloping.degreeFiltrationLT ℂ (ComplexLieAlgebra K n) d

theorem envelopingDegreeFiltration_mono : Monotone (envelopingDegreeFiltration K n) :=
  Langlands.Algebra.UniversalEnveloping.degreeFiltration_mono ℂ (ComplexLieAlgebra K n)

theorem envelopingDegreeFiltration_mul (p q : ℕ) :
    envelopingDegreeFiltration K n p * envelopingDegreeFiltration K n q =
      envelopingDegreeFiltration K n (p + q) :=
  Langlands.Algebra.UniversalEnveloping.degreeFiltration_mul ℂ (ComplexLieAlgebra K n) p q

theorem envelopingGenerator_mem_degreeFiltration (X : ComplexLieAlgebra K n) :
    envelopingGenerator K n X ∈ envelopingDegreeFiltration K n 1 := by
  simpa only [envelopingDegreeFiltration, envelopingGenerator,
    Langlands.Algebra.UniversalEnveloping.degreeFiltration_one] using
    Langlands.Algebra.UniversalEnveloping.generator_mem_degreeOne ℂ
      (ComplexLieAlgebra K n) X

theorem exists_mem_envelopingDegreeFiltration (a : EnvelopingAlgebra K n) :
    ∃ d, a ∈ envelopingDegreeFiltration K n d :=
  Langlands.Algebra.UniversalEnveloping.exists_mem_degreeFiltration ℂ
    (ComplexLieAlgebra K n) a

theorem iSup_envelopingDegreeFiltration : (⨆ d, envelopingDegreeFiltration K n d) = ⊤ :=
  Langlands.Algebra.UniversalEnveloping.iSup_degreeFiltration ℂ (ComplexLieAlgebra K n)

theorem commutator_mem_envelopingDegreeFiltration {p q : ℕ} {a b : EnvelopingAlgebra K n}
    (ha : a ∈ envelopingDegreeFiltration K n p)
    (hb : b ∈ envelopingDegreeFiltration K n q) :
    a * b - b * a ∈ envelopingDegreeFiltration K n (p + q - 1) :=
  Langlands.Algebra.UniversalEnveloping.commutator_mem_degreeFiltration ℂ
    (ComplexLieAlgebra K n) ha hb

section NumberField

variable [NumberField K]

local instance : FiniteDimensional ℝ (RealLieAlgebra K n) :=
  FiniteDimensional.of_injective (realLieAlgebraToMatrix K n).toLinearMap
    (realLieAlgebraToMatrix K n).injective

/-- Every finite degree piece is finite-dimensional for each number field and rank. -/
instance envelopingDegreeFiltration_finite (d : ℕ) :
    Module.Finite ℂ (envelopingDegreeFiltration K n d) :=
  Langlands.Algebra.UniversalEnveloping.degreeFiltration_finite ℂ
    (ComplexLieAlgebra K n) d

end NumberField

end Langlands.Global.ArchimedeanGL
