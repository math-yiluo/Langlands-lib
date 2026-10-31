import Langlands.Shimura.PEL.HarrisAdelicFrameFaithfulness
import Langlands.AlgebraicGeometry.Picard.DualRationalBaseChange
import Langlands.AlgebraicGeometry.Picard.PolarizationBaseChangeStatement
import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeProof

/-! # Actual pointed pullback of a positive Harris polarized action -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})


include dualityNaturality polarizationStability in
/-- Construct the actual changed positive polarized action. Faithfulness is
derived from the actual pointed Harris frame, not assumed for the output. -/
def framedPositiveActionBaseChange
    {S T : Scheme.{0}} (b : T ⟶ S)
    (X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := S)) :
    letI := auxiliaryStarRing D C
    ∀
  (hXb : HasDualScheme ((baseChange b).obj X.actionObj.abelianScheme))
  (_geometryXb : DualSchemeGeometry ((baseChange b).obj X.actionObj.abelianScheme) hXb)
  (Mb : LineBundle ((relativeSpace ((baseChange b).obj X.actionObj.abelianScheme).X.hom).obj
    (dualScheme ((baseChange b).obj X.actionObj.abelianScheme) hXb)))
  (_evaluationXb :
    tensorObj (poincareFamily ((baseChange b).obj X.actionObj.abelianScheme) hXb).obj.carrier
      Mb.obj ≅
    structureSheaf ((relativeSpace ((baseChange b).obj X.actionObj.abelianScheme).X.hom).obj
      (dualScheme ((baseChange b).obj X.actionObj.abelianScheme) hXb)))
  (_additivityXb : DualSchemeMapAdditivity preservation stability
    ((baseChange b).obj X.actionObj.abelianScheme)
    ((baseChange b).obj X.actionObj.abelianScheme) hXb hXb)
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (t : Spec (.of Ω) ⟶ T)
  (_frameExists :
    Nonempty (letI := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
      Tate.AdelicFrame X.actionObj.abelianScheme h X.actionObj.action
        ((Global.FiniteAdeles ℚ) ⊗[ℚ] A) (t ≫ b))),
    PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := T) := by
  letI := auxiliaryStarRing D C
  intro hXb geometryXb Mb evaluationXb additivityXb h Ω _ t frameExists
  refine
    { actionObj := (RationalAlgebraAction.pullback b).obj X.actionObj
      hasDual := hXb
      geometry := geometryXb
      inversePoincare := Mb
      evaluation := evaluationXb
      dualEndAdditivity := additivityXb
      polarization := dualAbelianBaseChangeMap preservation stability composition unitCoherence
        associativity comparison symmetry universality dualAbelianBaseChange b
        X.actionObj.abelianScheme X.hasDual X.geometry X.inversePoincare X.evaluation
        hXb geometryXb Mb evaluationXb X.polarization
      isPolarization := ?_
      faithful := ?_
      involutionCompatible := ?_ }
  · exact polarizationStability preservation square universality stability composition
      unitCoherence associativity comparison symmetry dualAbelianBaseChange S T b
      X.actionObj.abelianScheme X.hasDual X.geometry X.inversePoincare X.evaluation
      hXb geometryXb Mb evaluationXb X.polarization X.isPolarization
  · exact action_baseChange_injective_of_nonempty_adelicFrame D C
      X.actionObj.abelianScheme h X.actionObj.action b t frameExists
  · have hh := IsInvolutionCompatible.baseChange_of_naturality preservation stability
      composition unitCoherence associativity comparison symmetry universality
      dualAbelianBaseChange b X.actionObj.abelianScheme X.hasDual X.geometry
      X.inversePoincare X.evaluation hXb geometryXb Mb evaluationXb
      X.dualEndAdditivity additivityXb dualityNaturality X.involutionCompatible
    change IsInvolutionCompatible preservation composition unitCoherence associativity
      comparison symmetry stability hXb additivityXb Mb evaluationXb geometryXb
      ((rationalBaseChangeEnd b X.actionObj.abelianScheme).toRingHom.comp
        X.actionObj.action.toRingHom)
      (rationalDualBaseChangeHom preservation stability composition unitCoherence associativity
        comparison symmetry universality dualAbelianBaseChange b X.actionObj.abelianScheme
        X.hasDual X.geometry X.inversePoincare X.evaluation hXb geometryXb Mb evaluationXb
        (homToHom0 X.polarization)) at hh
    rw [rationalDualBaseChangeHom_homToHom0] at hh
    exact hh


end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
