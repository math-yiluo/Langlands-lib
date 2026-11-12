import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.NumberTheory.LocalField.Basic

/-! # The anisotropic quadratic dimension bound over nonarchimedean local fields -/

universe u v

namespace Langlands

/-- Every anisotropic quadratic form over a nonarchimedean local field has dimension
at most four, with no restriction on the characteristic or polar radical. -/
def LocalQuadraticAnisotropicDimensionBoundStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V), Q.Anisotropic → Module.finrank K V ≤ 4

end Langlands
