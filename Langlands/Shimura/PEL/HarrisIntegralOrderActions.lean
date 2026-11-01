import Langlands.Shimura.PEL.HarrisIntegralOrder
import Langlands.AbelianScheme.IntegralOrderActions
import Langlands.Algebra.IntegralOrderExtension
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Finite equations and rational extension for the actual Harris order -/

noncomputable section

open CategoryTheory AlgebraicGeometry Module

universe u v w s

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

instance harrisHodgePELIntegralOrder_free :
    Module.Free ℤ (D.harrisHodgePELIntegralOrder C) :=
  Submodule.IsLattice.free ℚ (D.harrisHodgePELIntegralOrder C).toSubmodule

/-- A finite integer basis of the already constructed positive-Harris order. -/
def harrisHodgePELIntegralBasis :
    Basis (Fin (Module.finrank ℤ (D.harrisHodgePELIntegralOrder C)))
      ℤ (D.harrisHodgePELIntegralOrder C) :=
  Module.finBasis ℤ (D.harrisHodgePELIntegralOrder C)

variable {S S' : Scheme.{s}}

/-- Actual actions of this order are solutions of its finite structure equations. -/
def harrisHodgePELIntegralActionEquiv (B : Langlands.AbelianScheme S) :
    ((D.harrisHodgePELIntegralOrder C) →+* CategoryTheory.End B) ≃
      AbelianScheme.IntegralActionSolutions (D.harrisHodgePELIntegralBasis C) B :=
  AbelianScheme.integralActionEquiv (D.harrisHodgePELIntegralBasis C) B

/-- Rationalize a supplied integral action, then extend uniquely from the full order. -/
def harrisHodgePELRationalAction (B : Langlands.AbelianScheme S)
    (a : (D.harrisHodgePELIntegralOrder C) →+* CategoryTheory.End B) :
    A →ₐ[ℚ] AbelianScheme.End0 B :=
  IntegralOrderExtension.extend (D.harrisHodgePELIntegralBasis C)
    ((Rationalization.ofEnd B).comp a)

@[simp] theorem harrisHodgePELRationalAction_coe (B : Langlands.AbelianScheme S)
    (a : (D.harrisHodgePELIntegralOrder C) →+* CategoryTheory.End B)
    (x : D.harrisHodgePELIntegralOrder C) :
    D.harrisHodgePELRationalAction C B a (x : A) = Rationalization.ofEnd B (a x) :=
  IntegralOrderExtension.extend_coe (D.harrisHodgePELIntegralBasis C) _ x

/-- Agreement on the actual full Harris order determines the whole rational action. -/
theorem harrisHodgePELRationalAction_unique (B : Langlands.AbelianScheme S)
    (a : (D.harrisHodgePELIntegralOrder C) →+* CategoryTheory.End B)
    (g : A →ₐ[ℚ] AbelianScheme.End0 B)
    (h : ∀ x : D.harrisHodgePELIntegralOrder C,
      g (x : A) = Rationalization.ofEnd B (a x)) :
    D.harrisHodgePELRationalAction C B a = g :=
  IntegralOrderExtension.extend_unique (D.harrisHodgePELIntegralBasis C) _ g h

/-- The finite-equation correspondence uses the published actual action pullback. -/
theorem harrisHodgePELIntegralActionEquiv_baseChange (c : S' ⟶ S)
    (B : Langlands.AbelianScheme S)
    (a : (D.harrisHodgePELIntegralOrder C) →+* CategoryTheory.End B) :
    D.harrisHodgePELIntegralActionEquiv C ((AbelianScheme.baseChange c).obj B)
        (AbelianScheme.baseChangeOrderAction c B a) =
      AbelianScheme.integralActionSolutionsBaseChange (D.harrisHodgePELIntegralBasis C)
        c B (D.harrisHodgePELIntegralActionEquiv C B a) :=
  AbelianScheme.integralActionEquiv_baseChange (D.harrisHodgePELIntegralBasis C) c B a

/-- Unique rational extension commutes with every actual scheme base change. -/
theorem harrisHodgePELRationalAction_baseChange (c : S' ⟶ S)
    (B : Langlands.AbelianScheme S)
    (a : (D.harrisHodgePELIntegralOrder C) →+* CategoryTheory.End B) :
    D.harrisHodgePELRationalAction C ((AbelianScheme.baseChange c).obj B)
        (AbelianScheme.baseChangeOrderAction c B a) =
      (AbelianScheme.rationalBaseChangeEnd c B).comp
        (D.harrisHodgePELRationalAction C B a) := by
  apply IntegralOrderExtension.algHom_ext (D.harrisHodgePELIntegralBasis C)
  intro x
  simp only [harrisHodgePELRationalAction_coe, AlgHom.comp_apply,
    AbelianScheme.baseChangeOrderAction_apply, AbelianScheme.rationalBaseChangeEnd_ofEnd]

end Langlands.Shimura.CentralSimpleUnitaryData
