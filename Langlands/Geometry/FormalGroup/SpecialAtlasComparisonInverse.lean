import Langlands.Geometry.FormalGroup.AtlasOrderComparisonInverse
import Langlands.Geometry.FormalGroup.SpecialAtlasClassReduction

/-! # Inverting actual special-atlas comparisons through quotient reduction -/

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
variable {X Y : (letI := α; SpecialAtlas K D ι R)}

/-- Transport of equal scalar structures retains the actual inverse comparison. -/
theorem reAlgebraComparison_symm (g : (letI := α; Comparison X Y))
    (β : Algebra 𝒪[K] R) (e : α = β) :
    (letI := α; reAlgebraComparison g.symm β e) =
      (letI := β; (reAlgebraComparison g β e).symm) := by
  cases e
  rfl

end AlgebraTransport

variable [Algebra 𝒪[K] R] [Algebra 𝒪[K] S]

/-- Supplied-target extension preserves the inverse of the specified formal comparison. -/
theorem baseChangeAlongComparison_symm {X Y : SpecialAtlas K D ι R}
    (g : Comparison X Y) (f : R →ₐ[𝒪[K]] S) :
    baseChangeAlongComparison g.symm f = (baseChangeAlongComparison g f).symm := by
  unfold baseChangeAlongComparison baseChangeComparison
  rw [BasicAtlas.OrderAction.Comparison.baseChange_symm]
  exact reAlgebraComparison_symm (baseChangeComparison g (BasicAtlas.coefficientTest f))
    _ (BasicAtlas.coefficientAlgebraAlong_eq f)

variable {r : R} {A : Nilp.{v, u} R r}

/-- Quotient reduction preserves the inverse of the same actual refined comparison. -/
theorem reductionComparison_symm {X Y : SpecialAtlas K D ι A.obj}
    (g : Comparison X Y) :
    reductionComparison g.symm = (reductionComparison g).symm :=
  baseChangeAlongComparison_symm g (Nilp.quotientO 𝒪[K] A)

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
