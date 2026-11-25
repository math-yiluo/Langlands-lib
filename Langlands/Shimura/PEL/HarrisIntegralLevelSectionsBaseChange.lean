import Langlands.Shimura.PEL.HarrisIntegralLevelSections
import Langlands.Shimura.PEL.HarrisIntegralNormalizationBaseChange

/-! # Base change of Harris level sections -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
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
  (P : Prerequisites.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  {S T : Scheme.{0}} (b : T ⟶ S)
  [QuasiSeparatedSpace S] [QuasiSeparatedSpace T]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (t : Spec (.of Ω) ⟶ T)

local notation "PObjS" =>
  letI := auxiliaryStarRing D C
  PositivePolarizedAction D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality (S := S)
local notation "DualData" X:max => PositivePullbackDualData D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality b X
local notation:max "BOf" X:max =>
  letI := auxiliaryStarRing D C
  (X).actionObj.abelianScheme
local notation "FrameAt" X:max s₀:max =>
  letI := auxiliaryStarRing D C
  Tate.WeilAdelicFrame P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability (X).hasDual
  (X).geometry (X).inversePoincare (X).evaluation compatibility (X).polarization h
  (X).actionObj.action A (D.harrisHodgePELForm C) s₀
local notation "pullObj" X:max W:max frameExists:max =>
  letI := auxiliaryStarRing D C
  framedPositiveActionBaseChange D C P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability P.square P.universality
  dualityNaturality polarizationStability b X (W).hasDual (W).geometry
  (W).inversePoincare (W).evaluation (W).dualEndAdditivity h t frameExists
local notation "frameBC" X:max W:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameBaseChange b (X).actionObj.abelianScheme P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.universality
  (X).hasDual (X).geometry (X).inversePoincare (X).evaluation (W).hasDual (W).geometry
  (W).inversePoincare (W).evaluation compatibility (X).polarization h
  (X).actionObj.action A (D.harrisHodgePELForm C) t
local notation "NormalizedAt" s₀:max =>
  HarrisIntegralFrameCondition D C P compatibility h s₀
local notation "FrameExists" X:max =>
  Nonempty (letI := auxiliaryStarRing D C
    letI := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
    Tate.AdelicFrame (X).actionObj.abelianScheme h (X).actionObj.action
      ((Global.FiniteAdeles ℚ) ⊗[ℚ] A) (t ≫ b))
local notation:max "redAt" X:max s₀:max =>
  harrisIntegralFrameReduction D C P compatibility h s₀ X
local notation:max "fullAt" X:max s₀:max =>
  harrisIntegralFrameFull D C P compatibility h s₀ X

/-- Reduction of the base-changed normalized frame is inverse finite torsion
base change of the reduction of the original frame at the pushed point. -/
theorem harrisIntegralFrameReduction_baseChange (X : PObjS) (W : DualData X)
    (frameExists : FrameExists X) (m : Index (fun _ => True))
    (eta : FrameAt X (t ≫ b)) (hn : (NormalizedAt (t ≫ b)) X eta) :
    ∀ (hn' : (NormalizedAt t) (pullObj X W frameExists) ((frameBC X W).symm eta))
      (q : HarrisIntegralSourceMod D C m.val),
      (redAt (pullObj X W frameExists) t) m ((frameBC X W).symm eta) hn' q =
        (GroupScheme.Tate.levelBaseChange b (BOf X).toGrp (Over.mk t) m.val).symm
          ((redAt X (t ≫ b)) m eta hn q) := by
  let := auxiliaryStarRing D C
  intro hn' q
  obtain ⟨v, rfl⟩ := (harrisIntegralSourceMultiples D C m.val).mkQ_surjective q
  rw [harrisIntegralFrameReduction_mkQ, harrisIntegralFrameReduction_mkQ]
  have hf : (fullAt (pullObj X W frameExists) t) ((frameBC X W).symm eta) hn' v =
      (Tate.integralBaseChange b (BOf X) (Over.mk t) (fun _ => True)).symm
        ((fullAt X (t ≫ b)) eta hn v) := by
    apply GroupScheme.Tate.full_toRational_injective (BOf (pullObj X W frameExists)).toGrp
      (Over.mk t)
    apply (Tate.rationalBaseChange b (BOf X) (Over.mk t) (fun _ => True)).injective
    rw [harrisIntegralFrameFull_toRational]
    change Tate.rationalBaseChange b (BOf X) (Over.mk t) (fun _ => True)
        (((frameBC X W).symm eta).1 v) =
      GroupScheme.Tate.toRational (BOf X).toGrp (Over.mk (t ≫ b)) (fun _ => True)
        ((Tate.integralBaseChange b (BOf X) (Over.mk t) (fun _ => True))
          ((Tate.integralBaseChange b (BOf X) (Over.mk t) (fun _ => True)).symm
            ((fullAt X (t ≫ b)) eta hn v)))
    rw [ContinuousLinearEquiv.apply_symm_apply, harrisIntegralFrameFull_toRational,
      Tate.weilAdelicFrameBaseChange_symm_apply, LinearEquiv.apply_symm_apply]
  rw [hf]
  rfl

variable
  (ht : ∀ Y : Cover T, Finite (Fiber t Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T k.val).X.hom]
  [hμetT : ∀ k : Index (fun _ => True), Etale (mu T k.val).X.hom]

local notation "ULevel" => FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)
local notation "Cong" => harrisIntegralAdeleCongruence D C
local notation "towerAt" X:max s₀:max hs₀:max hu₀:max =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.levelTower P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h A (D.harrisHodgePELForm C) s₀ hs₀ htor hu₀ X
local notation "LevelNormalizedAt" s₀:max hs₀:max hu₀:max =>
  HarrisIntegralLevelCondition D C P compatibility h s₀ hs₀ htor hu₀
local notation "rightAt" X:max s₀:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameRightAction P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability (X).hasDual (X).geometry
  (X).inversePoincare (X).evaluation compatibility (X).polarization h
  (X).actionObj.action A (D.harrisHodgePELForm C) s₀
local notation "levelBC" X:max W:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicLevelBaseChange b (X).actionObj.abelianScheme P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.universality
  (X).hasDual (X).geometry (X).inversePoincare (X).evaluation (W).hasDual (W).geometry
  (W).inversePoincare (W).evaluation compatibility (X).polarization h
  (X).actionObj.action A (D.harrisHodgePELForm C) t ht hs htor huS huT
local notation "orbitBC" X:max W:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameRightOrbitBaseChange b (X).actionObj.abelianScheme
  P.preservation P.composition P.unitCoherence P.associativity P.comparison
  P.symmetry P.stability P.universality (X).hasDual (X).geometry
  (X).inversePoincare (X).evaluation (W).hasDual (W).geometry
  (W).inversePoincare (W).evaluation compatibility (X).polarization h
  (X).actionObj.action A (D.harrisHodgePELForm C) t

/-- Base change along `b` of normalized invariant Harris orbits at a fixed level:
the published fixed-orbit pullback, restricted to normalized orbits, which it
preserves. -/
def harrisIntegralNormalizedLevelBaseChange (X : PObjS) (W : DualData X)
    (frameExists : FrameExists X) (U : ULevel) :
    {x : (towerAt X (t ≫ b) hs huS).obj U // (LevelNormalizedAt (t ≫ b) hs huS) X U x} →
      {y : (towerAt (pullObj X W frameExists) t ht huT).obj U //
        (LevelNormalizedAt t ht huT) (pullObj X W frameExists) U y} := fun x =>
  ⟨(levelBC X W) U.toSubgroup x.val,
    (harrisIntegralLevelCondition_baseChange D C P dualityNaturality polarizationStability b
      compatibility h t ht hs htor huS huT X W frameExists U x.val).mpr x.property⟩

@[simp] theorem harrisIntegralNormalizedLevelBaseChange_val (X : PObjS) (W : DualData X)
    (frameExists : FrameExists X) (U : ULevel)
    (x : {x : (towerAt X (t ≫ b) hs huS).obj U // (LevelNormalizedAt (t ≫ b) hs huS) X U x}) :
    (harrisIntegralNormalizedLevelBaseChange D C P dualityNaturality polarizationStability b
      compatibility h t ht hs htor huS huT X W frameExists U x).val =
      (levelBC X W) U.toSubgroup x.val := rfl

/-- Base change of normalized orbits is injective. -/
theorem harrisIntegralNormalizedLevelBaseChange_injective (X : PObjS) (W : DualData X)
    (frameExists : FrameExists X) (U : ULevel) :
    Function.Injective (harrisIntegralNormalizedLevelBaseChange D C P dualityNaturality
      polarizationStability b compatibility h t ht hs htor huS huT X W frameExists U) := by
  let := auxiliaryStarRing D C
  let _ := rightAt X (t ≫ b)
  let _ := rightAt (pullObj X W frameExists) t
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact ((orbitBC X W) U.toSubgroup).symm.injective
    (congrArg (fun z => z.val.val) hxy)

section Global

variable [ConnectedSpace S] [IsLocallyNoetherian S] [ConnectedSpace T] [IsLocallyNoetherian T]
  [IsAlgClosed Ω]

set_option maxHeartbeats 1000000 in
/-- Global level sections are natural under actual base change: the sections of the
pulled-back normalized orbit on `T` correspond, under torsion base change, to the
pullbacks along `b` of the sections of the original orbit on `S`. -/
theorem harrisIntegralLevelSections_baseChange (X : PObjS) (W : DualData X)
    (frameExists : FrameExists X) (m : Index (fun _ => True))
    (U : ULevel) (hU : U.toSubgroup ≤ Cong m.val)
    (x : (towerAt X (t ≫ b) hs huS).obj U)
    (hx : (LevelNormalizedAt (t ≫ b) hs huS) X U x)
    (q : HarrisIntegralSourceMod D C m.val) :
    GroupScheme.Tate.levelBaseChange b (BOf X).toGrp (Over.mk (𝟙 T)) m.val
        (harrisIntegralLevelSections D C P t ht htor huT compatibility h
          (pullObj X W frameExists) m U hU ((levelBC X W) U.toSubgroup x)
          ((harrisIntegralLevelCondition_baseChange D C P dualityNaturality
            polarizationStability b compatibility h t ht hs htor huS huT X W frameExists
            U x).mpr hx) q) =
      GroupScheme.Tate.levelRestrict (BOf X).toGrp
        (Over.homMk (𝟙 T ≫ b) (by simp) :
          (Over.map b).obj (Over.mk (𝟙 T)) ⟶ Over.mk (𝟙 S)) m.val
        (harrisIntegralLevelSections D C P (t ≫ b) hs htor huS compatibility h X m U hU
          x hx q) := by
  let := auxiliaryStarRing D C
  let _ := rightAt X (t ≫ b)
  let _ := rightAt (pullObj X W frameExists) t
  let B := BOf X
  let lbcT := GroupScheme.Tate.levelBaseChange b B.toGrp (Over.mk (𝟙 T)) m.val
  let lbct := GroupScheme.Tate.levelBaseChange b B.toGrp (Over.mk t) m.val
  let aT : Over.mk t ⟶ Over.mk (𝟙 T) := Over.homMk t (by simp)
  let aB : (Over.map b).obj (Over.mk (𝟙 T)) ⟶ Over.mk (𝟙 S) := Over.homMk (𝟙 T ≫ b) (by simp)
  obtain ⟨eta, hn, heta⟩ := id hx
  have hn' := (harrisIntegralFrameCondition_baseChange D C P dualityNaturality
    polarizationStability b compatibility h t X W frameExists eta).mpr hn
  have heta' : RightOrbit.mk U.toSubgroup ((frameBC X W).symm eta) =
      ((levelBC X W) U.toSubgroup x).val := by
    change RightOrbit.mk U.toSubgroup ((frameBC X W).symm eta) =
      ((orbitBC X W) U.toSubgroup).symm x.val
    rw [← heta, Tate.weilAdelicFrameRightOrbitBaseChange_symm_mk]
  rw [← lbcT.apply_symm_apply (GroupScheme.Tate.levelRestrict B.toGrp aB m.val _)]
  congr 1
  apply (harrisIntegralGlobalTorsionEquiv D C P t ht htor huT (pullObj X W frameExists) m).injective
  apply Subtype.ext
  rw [harrisIntegralGlobalTorsionEquiv_apply, harrisIntegralGlobalTorsionEquiv_apply]
  refine (harrisIntegralLevelSections_restrict D C P t ht htor huT compatibility h
    (pullObj X W frameExists) m U hU _ _ q).trans ?_
  refine (harrisIntegralLevelReduction_apply D C P compatibility h t ht htor huT
    (pullObj X W frameExists) m U hU _ _ ((frameBC X W).symm eta) hn' heta' q).trans ?_
  refine (harrisIntegralFrameReduction_baseChange D C P dualityNaturality
    polarizationStability b compatibility h t X W frameExists m eta hn hn' q).trans ?_
  rw [← harrisIntegralLevelReduction_apply D C P compatibility h (t ≫ b) hs htor huS X m U hU
    x hx eta hn heta q, ← harrisIntegralLevelSections_restrict D C P (t ≫ b) hs htor huS
    compatibility h X m U hU x hx q]
  apply lbct.injective
  rw [AddEquiv.apply_symm_apply]
  refine Eq.trans ?_ (GroupScheme.Tate.levelBaseChange_testRestrict b B.toGrp aT m.val _).symm
  rw [AddEquiv.apply_symm_apply]
  apply GroupScheme.Tate.toSection_injective B.toGrp _ m.val
  apply Additive.toMul.injective
  rw [GroupScheme.Tate.toSection_levelRestrict]
  refine Eq.trans ?_ (Category.assoc ((Over.map b).map aT) aB _)
  congr 1

end Global

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
