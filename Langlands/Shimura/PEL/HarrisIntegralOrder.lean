import Langlands.Shimura.PEL.IntegralOrder
import Langlands.Shimura.PEL.HarrisHodgeInput

/-! # An integral order for the actual positive Harris left involution -/

noncomputable section

universe u v w

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra

variable {E : Type u} {K : Type v} {A : Type w}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (D : CentralSimpleUnitaryData E K A n)
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

include D in
private theorem rationalFinite : FiniteDimensional ℚ A := by
  have : Module.Finite E A := Module.Finite.of_basis D.totallyRealBasis
  exact FiniteDimensional.trans ℚ E A

/-- A concrete finite full lattice in the actual rational regular module. -/
def harrisHodgePELLattice : Submodule ℤ A :=
  letI := rationalFinite D
  PEL.basisLattice A

instance harrisHodgePELLattice_isLattice :
    Submodule.IsLattice ℚ D.harrisHodgePELLattice := by
  have := rationalFinite D
  exact PEL.basisLattice_isLattice A

@[simp] theorem one_mem_harrisHodgePELLattice :
    (1 : A) ∈ D.harrisHodgePELLattice := by
  have := rationalFinite D
  exact PEL.one_mem_basisLattice A

/-- The finite full order uses the positive auxiliary left involution. -/
def harrisHodgePELIntegralOrder : Subalgebra ℤ A :=
  letI := rationalFinite D
  PEL.integralOrder A
    (D.harrisHodgePELAlgebra C).toSecondKindInvolution.rationalInvolution

instance harrisHodgePELIntegralOrder_finite :
    Module.Finite ℤ (D.harrisHodgePELIntegralOrder C) := by
  have := rationalFinite D
  exact PEL.integralOrder_finite A _

instance harrisHodgePELIntegralOrder_isLattice :
    Submodule.IsLattice ℚ (D.harrisHodgePELIntegralOrder C).toSubmodule := by
  have := rationalFinite D
  exact PEL.integralOrder_isLattice A _

theorem exists_int_multiple_mem_harrisHodgePELIntegralOrder (a : A) :
    ∃ m : ℤ, m ≠ 0 ∧ m • a ∈ D.harrisHodgePELIntegralOrder C := by
  have := rationalFinite D
  exact PEL.exists_int_multiple_mem_integralOrder A _ a

@[simp] theorem involution_mem_harrisHodgePELIntegralOrder (a : A) :
    (D.harrisHodgePELAlgebra C).involution a ∈ D.harrisHodgePELIntegralOrder C ↔
      a ∈ D.harrisHodgePELIntegralOrder C := by
  have := rationalFinite D
  exact PEL.involution_mem_integralOrder A _ a

/-- Restriction of the same positive left involution to the integral order. -/
def harrisHodgePELIntegralInvolution :
    AlgebraInvolution ℤ (D.harrisHodgePELIntegralOrder C) :=
  letI := rationalFinite D
  PEL.integralOrderInvolution A _

@[simp] theorem harrisHodgePELIntegralInvolution_apply
    (a : D.harrisHodgePELIntegralOrder C) :
    (D.harrisHodgePELIntegralInvolution C a : A) =
      (D.harrisHodgePELAlgebra C).involution a := rfl

/-- The constructed order acts on the actual lattice by left multiplication. -/
def harrisHodgePELIntegralAction :
    D.harrisHodgePELIntegralOrder C →+* Module.End ℤ D.harrisHodgePELLattice :=
  letI := rationalFinite D
  PEL.integralOrderAction A _

@[simp] theorem harrisHodgePELIntegralAction_apply
    (a : D.harrisHodgePELIntegralOrder C) (x : D.harrisHodgePELLattice) :
    (D.harrisHodgePELIntegralAction C a x : A) = (a : A) * x := rfl

theorem harrisHodgePELIntegralAction_injective :
    Function.Injective (D.harrisHodgePELIntegralAction C) := by
  have := rationalFinite D
  exact PEL.integralOrderAction_injective A _

theorem harrisHodgePELIntegralAction_adjoint
    (a : D.harrisHodgePELIntegralOrder C) (x y : D.harrisHodgePELLattice) :
    D.harrisHodgePELForm C (D.harrisHodgePELIntegralAction C a x : A) (y : A) =
      D.harrisHodgePELForm C (x : A)
        (D.harrisHodgePELIntegralAction C (D.harrisHodgePELIntegralInvolution C a) y : A) :=
  D.harrisHodgePELForm_left C a x y

theorem harrisHodgePELIntegralOrder_mul_mem_lattice
    {a x : A} (ha : a ∈ D.harrisHodgePELIntegralOrder C)
    (hx : x ∈ D.harrisHodgePELLattice) :
    a * x ∈ D.harrisHodgePELLattice := by
  have := rationalFinite D
  exact PEL.integralOrder_mul_mem_basisLattice A _ ha hx

end Langlands.Shimura.CentralSimpleUnitaryData
