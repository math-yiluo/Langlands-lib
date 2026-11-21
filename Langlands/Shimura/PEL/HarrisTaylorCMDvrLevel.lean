import Langlands.Shimura.PEL.HarrisTaylorCMDvrMonodromy
import Langlands.Shimura.PEL.HarrisTaylorCMArtinianLevel

/-! # The actual pointed Harris level over a discrete valuation ring -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.GroupScheme
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)

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
  {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)

variable
  {Ω : Type} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of K))
  (ht : ∀ Y : Cover (Spec (.of K)), Finite (Fiber t Y))
  (hs : ∀ Y : Cover (Spec (.of V)), Finite (Fiber (t ≫ Spec.algebraMap V K) Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Spec (.of V), ⊤)))
  (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Spec (.of K), ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu (Spec (.of V)) k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu (Spec (.of V)) k.val).X.hom]
  [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu (Spec (.of K)) k.val).X.hom]
  [hμetT : ∀ k : Index (fun _ => True), Etale (mu (Spec (.of K)) k.val).X.hom]
  (X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := Spec (.of V)))
  (W : PositivePullbackDualData D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (Spec.algebraMap V K) X)

local notation "j" => Spec.algebraMap V K

set_option quotPrecheck false in
local notation "GenericAction" => (rationalBaseChangeEnd j X.actionObj.abelianScheme).comp
  X.actionObj.action

set_option maxHeartbeats 800000 in
omit [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V K] [IsAlgClosed Ω]
  hμfinS hμetS hμfinT hμetT in
/-- An ambient frame on the actual generic action gives an ambient frame on
the model at the composite geometric point. -/
theorem dvrFrameExists_of_genericFrame
    (hg : letI := auxiliaryStarRing D C
      letI := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
      Nonempty (Tate.AdelicFrame ((AbelianScheme.baseChange j).obj X.actionObj.abelianScheme) h GenericAction
        ((Global.FiniteAdeles ℚ) ⊗[ℚ] A) t)) :
    letI := auxiliaryStarRing D C
    letI := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
    Nonempty (Tate.AdelicFrame X.actionObj.abelianScheme h X.actionObj.action
      ((Global.FiniteAdeles ℚ) ⊗[ℚ] A) (t ≫ j)) := by
  let := auxiliaryStarRing D C
  let := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
  exact hg.map (Tate.adelicFrameBaseChange j X.actionObj.abelianScheme h X.actionObj.action
    ((Global.FiniteAdeles ℚ) ⊗[ℚ] A) t)

set_option maxHeartbeats 2000000 in
/-- Extend an actual fixed level orbit on the canonically changed polarized
action to the DVR. The output carries its equation under the existing level pullback. -/
def extendDvrHarrisLevel
    (hg : letI := auxiliaryStarRing D C
      letI := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
      Nonempty (Tate.AdelicFrame ((AbelianScheme.baseChange j).obj X.actionObj.abelianScheme) h GenericAction
        ((Global.FiniteAdeles ℚ) ⊗[ℚ] A) t))
    (U : HarrisLevel D) :
    letI := auxiliaryStarRing D C
    let frameExists := dvrFrameExists_of_genericFrame D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality h t X hg
    let f := (framedPositiveActionTowerBaseChange D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability j compatibility h t ht hs htor huS huT X
      W.hasDual W.geometry W.inversePoincare W.evaluation W.dualEndAdditivity frameExists).app U
    ∀ q, {x // f x = q} := by
  letI := auxiliaryStarRing D C
  dsimp only
  intro q
  let frameExists := dvrFrameExists_of_genericFrame D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality h t X hg
  have hsurj := framedPositiveActionTowerBaseChange_surjective D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability j compatibility h t ht hs htor huS huT X W
    (dvrGenericMonodromy_surjective V K t ht hs) frameExists U
  exact ⟨Function.surjInv hsurj q, Function.surjInv_eq hsurj q⟩

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
