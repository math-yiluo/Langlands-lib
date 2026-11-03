import Langlands.AbelianScheme.IntegralOrderModelComparison
import Langlands.Shimura.PEL.HarrisIntegralOrderActions
import Langlands.Shimura.PEL.RationalLieDeterminantClasses

/-! # Integral models of the actual Harris order with determinant comparison -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AbelianScheme

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra

variable {E F A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field F] [NumberField F] [IsTotallyComplex F]
    [Algebra E F] [IsQuadraticExtension E F]
    [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
    {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
    {Φ : (E →+* ℝ) → (F →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
    (htor : TorsionFiniteEtaleStatement.{0})
    {S : Scheme.{0}} [IsLocallyNoetherian S]
    (p : S ⟶ Spec (.of (D.kottwitzCocharacterReflexField C)))
    (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B)
    (hfib : ∀ (F₀ : Finset B.X.left) (s : S), (∀ x ∈ F₀, B.X.hom x = s) →
      ∃ W : B.X.left.Opens, IsAffineOpen W ∧ ∀ x ∈ F₀, x ∈ W)

/-- An actual model for the constructed positive-Harris integer order, using the
original rational action and the explicit finite-fibre affine-open criterion. -/
def harrisIntegralOrderModel :
    IntegralOrderModel (D.harrisRationalOrderAction C B i) :=
  integralOrderModelOfForallFinsetFibre htor p (D.harrisHodgePELIntegralBasis C)
    (D.harrisRationalOrderAction C B i) hfib

local notation "M" => D.harrisIntegralOrderModel C htor p B i hfib
local notation "b" => D.harrisHodgePELIntegralBasis C

/-- The original full Harris rational algebra action is equivariantly isomorphic
to the full extension of the constructed actual integral action. -/
def harrisIntegralOrderModelIso :
    RationalAlgebraAction.of B i ≅
      RationalAlgebraAction.of (M).B (D.harrisHodgePELRationalAction C (M).B (M).action) :=
  IntegralOrderModel.rationalAlgebraIso b i M

/-- The full all-chart Harris determinant condition is preserved, and becomes the
existing integral Lie determinant condition for the constructed model. -/
theorem harrisIntegralOrderModel_determinant_iff (hΦ : IsCMSection E F Φ) :
    D.HarrisRationalLieDeterminantCondition C hΦ p B i ↔
      D.HarrisLieDeterminantCondition C hΦ p (M).B (M).action := by
  have h := D.harrisRationalLieDeterminantCondition_actionIso C hΦ p
    (D.harrisIntegralOrderModelIso C htor p B i hfib)
  exact h.trans (D.harrisRationalLieDeterminantCondition_iff_integral C hΦ p (M).B
    (D.harrisHodgePELRationalAction C (M).B (M).action) (M).action
    (fun x => (D.harrisHodgePELRationalAction_coe C (M).B (M).action x).symm))

end Langlands.Shimura.CentralSimpleUnitaryData
