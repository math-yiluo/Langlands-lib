import Langlands.Shimura.PEL.HarrisPolarizedActionBaseChange
import Langlands.AbelianScheme.Tate.WeilCompactOpenLevelBaseChange
import Mathlib.CategoryTheory.Whiskering

/-! # Pointed pullback of the original-index tower of an actual Harris polarized action -/

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
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
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
  {S T : Scheme.{0}} (b : T ⟶ S)
  [QuasiSeparatedSpace S] [QuasiSeparatedSpace T]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (t : Spec (.of Ω) ⟶ T)
  (ht : ∀ Y : Cover T, Finite (Fiber t Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T k.val).X.hom]
  [hμetT : ∀ k : Index (fun _ => True), Etale (mu T k.val).X.hom]
  (X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))

omit [QuasiSeparatedSpace T] hμfinT hμetT in
/-- An existing fixed level orbit contains an actual compatible frame, without
requiring a representative fixed by monodromy. -/
theorem level_nonempty_adelicFrame :
    letI := auxiliaryStarRing D C
    ∀ (U : HarrisLevel D)
      (_q : (PolarizedWeilLevel.levelTower preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h
        A (D.harrisHodgePELForm C) (t ≫ b) hs htor huS X).obj
          ((hodgeLevelFunctor D C).obj U)),
    Nonempty (letI := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
      Tate.AdelicFrame X.actionObj.abelianScheme h X.actionObj.action
        ((Global.FiniteAdeles ℚ) ⊗[ℚ] A) (t ≫ b)) := by
  let := auxiliaryStarRing D C
  intro U q
  let := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
  obtain ⟨eta, _⟩ := Quotient.exists_rep q.val
  exact ⟨eta.1⟩

/-- Reindex the actual pointed compatible-level pullback by the original Harris
level functor, with target the concretely constructed changed polarized action. -/
def framedPositiveActionTowerBaseChange :
    letI := auxiliaryStarRing D C
    ∀ (hXb : HasDualScheme ((Langlands.AbelianScheme.baseChange b).obj X.actionObj.abelianScheme))
      (geometryXb : DualSchemeGeometry ((Langlands.AbelianScheme.baseChange b).obj X.actionObj.abelianScheme) hXb)
      (Mb : LineBundle ((relativeSpace ((Langlands.AbelianScheme.baseChange b).obj X.actionObj.abelianScheme).X.hom).obj
        (dualScheme ((Langlands.AbelianScheme.baseChange b).obj X.actionObj.abelianScheme) hXb)))
      (evaluationXb :
        tensorObj (poincareFamily ((Langlands.AbelianScheme.baseChange b).obj X.actionObj.abelianScheme) hXb).obj.carrier
          Mb.obj ≅
        structureSheaf ((relativeSpace ((Langlands.AbelianScheme.baseChange b).obj X.actionObj.abelianScheme).X.hom).obj
          (dualScheme ((Langlands.AbelianScheme.baseChange b).obj X.actionObj.abelianScheme) hXb)))
      (additivityXb : DualSchemeMapAdditivity preservation stability
        ((Langlands.AbelianScheme.baseChange b).obj X.actionObj.abelianScheme)
        ((Langlands.AbelianScheme.baseChange b).obj X.actionObj.abelianScheme) hXb hXb)
      (frameExists :
        Nonempty (letI := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
          Tate.AdelicFrame X.actionObj.abelianScheme h X.actionObj.action
            ((Global.FiniteAdeles ℚ) ⊗[ℚ] A) (t ≫ b))),
    let Y := framedPositiveActionBaseChange D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability b X hXb geometryXb Mb evaluationXb additivityXb h t frameExists
    (hodgeLevelFunctor D C ⋙
      PolarizedWeilLevel.levelTower preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h
        A (D.harrisHodgePELForm C) (t ≫ b) hs htor huS X) ⟶
    (hodgeLevelFunctor D C ⋙
      PolarizedWeilLevel.levelTower preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h
        A (D.harrisHodgePELForm C) t ht htor huT Y) := by
  let := auxiliaryStarRing D C
  intro hXb geometryXb Mb evaluationXb additivityXb frameExists
  exact Functor.whiskerLeft (hodgeLevelFunctor D C)
    (Tate.weilAdelicCompactOpenLevelBaseChange b X.actionObj.abelianScheme
      preservation composition unitCoherence associativity comparison symmetry stability universality
      X.hasDual X.geometry X.inversePoincare X.evaluation hXb geometryXb Mb evaluationXb
      compatibility X.polarization h X.actionObj.action A (D.harrisHodgePELForm C)
      t ht hs htor huS huT)

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
