import Langlands.Geometry.FormalGroup.AtlasOrderComparisonIdentity
import Langlands.Geometry.FormalGroup.SpecialAtlasComparisonInverse

/-! # Actual diagonal comparisons through special-atlas quotient reduction -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R S : Type v} [CommRing R] [CommRing S]

attribute [local instance] coefficientAlgebra coefficientScalarTower

section AlgebraTransport

variable {α : Algebra 𝒪[K] R}
variable {X : (letI := α; SpecialAtlas K D ι R)}

/-- Retyping equal scalar structures retains an actual diagonal comparison. -/
theorem isDiagonal_reAlgebraComparison (g : (letI := α; Comparison X X))
    (h : (letI := α; g.IsDiagonal)) (β : Algebra 𝒪[K] R) (e : α = β) :
    (letI := β; (reAlgebraComparison g β e).IsDiagonal) := by
  cases e
  exact h

end AlgebraTransport

variable [Algebra 𝒪[K] R] [Algebra 𝒪[K] S]

/-- Extension to supplied target scalars retains the actual identity on a refinement. -/
theorem isDiagonal_baseChangeAlongComparison {X : SpecialAtlas K D ι R}
    (g : Comparison X X) (h : g.IsDiagonal) (f : R →ₐ[𝒪[K]] S) :
    (baseChangeAlongComparison g f).IsDiagonal :=
  isDiagonal_reAlgebraComparison (baseChangeComparison g (BasicAtlas.coefficientTest f))
    (h.baseChange (BasicAtlas.coefficientTest f)) _ (BasicAtlas.coefficientAlgebraAlong_eq f)

variable {r : R} {A : Nilp.{v, u} R r}

/-- The actual quotient extension preserves an identity comparison on a refinement. -/
theorem isDiagonal_reductionComparison {X : SpecialAtlas K D ι A.obj}
    (g : Comparison X X) (h : g.IsDiagonal) : (reductionComparison g).IsDiagonal :=
  isDiagonal_baseChangeAlongComparison g h (Nilp.quotientO 𝒪[K] A)

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
