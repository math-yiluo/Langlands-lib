import Langlands.Shimura.PEL.HarrisIntegralTateImages
import Langlands.Shimura.PEL.HarrisPolarizedClassBaseChange

/-! # Integral-normalization compatibility with actual Harris pullback -/

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

local notation "PObjS" => PositivePolarizedAction D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality (S := S)
local notation "DualData" X:max => PositivePullbackDualData D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality b X
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

omit [QuasiSeparatedSpace S] [QuasiSeparatedSpace T] in
private theorem fullImage_baseChange_iff (B : Langlands.AbelianScheme S)
    (z : Tate.Rational ((Langlands.AbelianScheme.baseChange b).obj B)
      (Over.mk t) (fun _ => True)) :
    (∃ x : GroupScheme.Tate.Full ((Langlands.AbelianScheme.baseChange b).obj B).toGrp
      (Over.mk t), GroupScheme.Tate.toRational _ (Over.mk t) (fun _ => True) x = z) ↔
    (∃ y : GroupScheme.Tate.Full B.toGrp (Over.mk (t ≫ b)),
      GroupScheme.Tate.toRational B.toGrp (Over.mk (t ≫ b)) (fun _ => True) y =
        Tate.rationalBaseChange b B (Over.mk t) (fun _ => True) z) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Tate.integralBaseChange b B (Over.mk t) (fun _ => True) x, rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := (Tate.integralBaseChange b B (Over.mk t) (fun _ => True)).surjective y
    refine ⟨x, (Tate.rationalBaseChange b B (Over.mk t) (fun _ => True)).injective ?_⟩
    exact hy

/-- Actual pointed pullback preserves and reflects full integral frame normalization. -/
theorem harrisIntegralFrameCondition_baseChange (X : PObjS) (W : DualData X)
    (frameExists : FrameExists X)
    (eta : FrameAt X (t ≫ b)) :
    (NormalizedAt t) (pullObj X W frameExists) ((frameBC X W).symm eta) ↔
      (NormalizedAt (t ≫ b)) X eta := by
  let := auxiliaryStarRing D C
  constructor
  · intro hn v
    have hb := fullImage_baseChange_iff b t X.actionObj.abelianScheme
      (((frameBC X W).symm eta).1 v)
    simp only [Tate.weilAdelicFrameBaseChange_symm_apply, LinearEquiv.apply_symm_apply] at hb
    exact (hn v).trans hb
  · intro hn v
    have hb := fullImage_baseChange_iff b t X.actionObj.abelianScheme
      (((frameBC X W).symm eta).1 v)
    simp only [Tate.weilAdelicFrameBaseChange_symm_apply, LinearEquiv.apply_symm_apply] at hb
    exact (hn v).trans hb.symm

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

local notation "Level" => FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)
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

/-- The existing fixed-orbit pullback preserves and reflects integral normalization. -/
theorem harrisIntegralLevelCondition_baseChange (X : PObjS) (W : DualData X)
    (frameExists : FrameExists X) (K : Level)
    (x : (towerAt X (t ≫ b) hs huS).obj K) :
    (LevelNormalizedAt t ht huT) (pullObj X W frameExists) K
      ((levelBC X W) K.toSubgroup x) ↔
    (LevelNormalizedAt (t ≫ b) hs huS) X K x := by
  let := auxiliaryStarRing D C
  let := rightAt X (t ≫ b)
  let := rightAt (pullObj X W frameExists) t
  constructor
  · rintro ⟨xi, hn, hxi⟩
    have hnorm := harrisIntegralFrameCondition_baseChange D C P dualityNaturality
      polarizationStability b compatibility h t X W frameExists ((frameBC X W) xi)
    rw [Equiv.symm_apply_apply] at hnorm
    refine ⟨(frameBC X W) xi, hnorm.mp hn, ?_⟩
    have heq := congrArg ((orbitBC X W) K.toSubgroup) hxi
    change RightOrbit.mk K.toSubgroup ((frameBC X W) xi) =
      ((orbitBC X W) K.toSubgroup) (((levelBC X W) K.toSubgroup x).val) at heq
    simpa only [Tate.weilAdelicLevelBaseChange_val, Equiv.apply_symm_apply] using heq
  · rintro ⟨eta, hn, heta⟩
    refine ⟨(frameBC X W).symm eta,
      (harrisIntegralFrameCondition_baseChange D C P dualityNaturality
        polarizationStability b compatibility h t X W frameExists eta).mpr hn, ?_⟩
    change RightOrbit.mk K.toSubgroup ((frameBC X W).symm eta) =
      ((orbitBC X W) K.toSubgroup).symm x.val
    rw [← heta, Tate.weilAdelicFrameRightOrbitBaseChange_symm_mk]

local notation "DataS" => HarrisLevelData D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality compatibility h (t ≫ b) hs htor huS
local notation "DataT" => HarrisLevelData D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality compatibility h t ht htor huT
local notation "pullData" dualData:max =>
  levelDataBaseChange D C P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability P.square P.universality
  dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData

/-- Normalization is preserved and reflected on the same original Harris representatives. -/
theorem harrisIntegralLevelCondition_levelDataBaseChange
    (dualData : ∀ X : PObjS, DualData X) (U : HarrisLevel D) (x : DataS U) :
    let y := (pullData dualData) U x
    (LevelNormalizedAt t ht huT) y.1 ((hodgeLevelFunctor D C).obj U) y.2 ↔
      (LevelNormalizedAt (t ≫ b) hs huS) x.1 ((hodgeLevelFunctor D C).obj U) x.2 := by
  let := auxiliaryStarRing D C
  let W := dualData x.1
  let frameExists := level_nonempty_adelicFrame D C P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
    P.universality b compatibility h t hs htor huS x.1 U x.2
  exact harrisIntegralLevelCondition_baseChange D C P dualityNaturality
    polarizationStability b compatibility h t ht hs htor huS huT x.1 W
    frameExists ((hodgeLevelFunctor D C).obj U) x.2

/-- Restrict the original representative pullback to integral-normalized data. -/
def harrisIntegralNormalizedLevelDataBaseChange
    (dualData : ∀ X : PObjS, DualData X) (U : HarrisLevel D) :
    {x : DataS U //
      (LevelNormalizedAt (t ≫ b) hs huS) x.1 ((hodgeLevelFunctor D C).obj U) x.2} →
    {y : DataT U //
      (LevelNormalizedAt t ht huT) y.1 ((hodgeLevelFunctor D C).obj U) y.2} :=
  fun x => ⟨(pullData dualData) U x.val,
    (harrisIntegralLevelCondition_levelDataBaseChange D C P dualityNaturality
      polarizationStability b compatibility h t ht hs htor huS huT
      dualData U x.val).mpr x.property⟩

/-- Forgetting integral normalization recovers the literal original pullback. -/
@[simp] theorem harrisIntegralNormalizedLevelDataBaseChange_val
    (dualData : ∀ X : PObjS, DualData X) (U : HarrisLevel D)
    (x : {x : DataS U //
      (LevelNormalizedAt (t ≫ b) hs huS) x.1 ((hodgeLevelFunctor D C).obj U) x.2}) :
    (harrisIntegralNormalizedLevelDataBaseChange D C P dualityNaturality
      polarizationStability b compatibility h t ht hs htor huS huT dualData U x).val =
      (pullData dualData) U x.val := rfl

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
