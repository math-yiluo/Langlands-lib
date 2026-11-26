import Langlands.Shimura.PEL.HarrisIntegralPrincipalFullLevel
import Langlands.Shimura.PEL.HarrisIntegralLevelSectionsPoint
import Langlands.Shimura.PEL.HarrisIntegralLevelSectionsBaseChange

/-! # Change of geometric point and base for principal Harris markings -/

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
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A] [IsScalarTower ℚ E F]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (P : Prerequisites.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)

local notation "gH" => Module.finrank ℚ E * n ^ 2
local notation "PObjAt" S₀:max =>
  letI := auxiliaryStarRing D C
  PositivePolarizedAction D C P.preservation P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability P.square P.universality (S := S₀)
local notation:max "BOf" X:max =>
  letI := auxiliaryStarRing D C
  (X).actionObj.abelianScheme
local notation "ULevel" => FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)
local notation "Cong" => harrisIntegralAdeleCongruence D C
local notation "LiftAt" s₀:max => HarrisPrincipalFullLevelCondition D C h P compatibility s₀

section Point

variable {S : Scheme.{0}} [QuasiSeparatedSpace S] [ConnectedSpace S] [IsLocallyNoetherian S]
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  {Ω Ω' : Type} [Field Ω] [Field Ω'] [IsAlgClosed Ω] [IsAlgClosed Ω']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)} {ht : ∀ Y : Cover S, Finite (Fiber t Y)}

local notation "PObj" => PObjAt S
local notation "towerAt" X:max s₀:max hs₀:max =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.levelTower P.preservation P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability P.square P.universality compatibility h A
    (D.harrisHodgePELForm C) s₀ hs₀ htor hu X
local notation "NormalizedAt" s₀:max hs₀:max =>
  HarrisIntegralLevelCondition D C P compatibility h s₀ hs₀ htor hu
local notation "pointEquiv" =>
  harrisIntegralNormalizedLevelPointEquiv D C P compatibility h htor hu
local notation "EquivAt" s₀:max hs₀:max =>
  harrisPrincipalFullLevelEquiv D C h P compatibility s₀ hs₀ htor hu

/-- Transport of the original normalized invariant orbit leaves the ordered marking unchanged. -/
theorem harrisPrincipalFullLevelEquiv_point (X : PObj)
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) (m : Index (fun _ => True))
    (U : ULevel) (hU : U.toSubgroup = Cong m.val)
    (x : {x : (towerAt X s hs).obj U // (NormalizedAt s hs) X U x}) :
    ((EquivAt t ht) X m U hU (pointEquiv X path U x)).val =
      ((EquivAt s hs) X m U hU x).val := by
  rw [harrisPrincipalFullLevelEquiv_apply_val, harrisPrincipalFullLevelEquiv_apply_val]
  apply fullLevel_eq_of_sections
  exact harrisIntegralOrderedFullLevel_normalizedTransport
    D C P compatibility h htor hu X path m U hU.le x

include htor hu hs ht in
/-- The compatible markings can be tested at either geometric point on a connected base. -/
theorem harrisPrincipalFullLevelCondition_iff_point
    (X : PObj) (m : Index (fun _ => True))
    (U : ULevel) (hU : U.toSubgroup = Cong m.val) (v : FullLevel (BOf X) gH m.val) :
    (LiftAt s) X m v ↔ (LiftAt t) X m v := by
  obtain ⟨path⟩ := geometricPathExists s t hs ht
  constructor
  · intro hv
    obtain ⟨x, hx⟩ := ((EquivAt s hs) X m U hU).surjective ⟨v, hv⟩
    let y := (pointEquiv X path U) x
    let w := (EquivAt t ht) X m U hU y
    have hw : w.val = v :=
      (harrisPrincipalFullLevelEquiv_point D C P compatibility h htor hu
        X path m U hU x).trans (congrArg Subtype.val hx)
    exact hw ▸ w.property
  · intro hv
    obtain ⟨y, hy⟩ := ((EquivAt t ht) X m U hU).surjective ⟨v, hv⟩
    let x := (pointEquiv X path.symm U) y
    let w := (EquivAt s hs) X m U hU x
    have hw : w.val = v :=
      (harrisPrincipalFullLevelEquiv_point D C P compatibility h htor hu
        X path.symm m U hU y).trans (congrArg Subtype.val hy)
    exact hw ▸ w.property

include htor hu hs ht in
/-- The canonical geometric-point comparison is the identity on the underlying global markings. -/
def harrisPrincipalFullLevelGeometricEquiv (X : PObj) (m : Index (fun _ => True))
    (U : ULevel) (hU : U.toSubgroup = Cong m.val) :
    {v : FullLevel (BOf X) gH m.val // (LiftAt s) X m v} ≃
      {v : FullLevel (BOf X) gH m.val // (LiftAt t) X m v} :=
  (Equiv.refl _).subtypeEquiv
    (harrisPrincipalFullLevelCondition_iff_point D C P compatibility h htor hu
      (hs := hs) (ht := ht) X m U hU)

end Point

section BaseChange

variable (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  {S T : Scheme.{0}} [QuasiSeparatedSpace S] [QuasiSeparatedSpace T]
  (b : T ⟶ S) {Ω : Type} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)

local notation "PObjS" => PObjAt S
local notation "DualData" X:max => PositivePullbackDualData D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality b X
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
local notation "FrameExists" X:max =>
  Nonempty (letI := auxiliaryStarRing D C
    letI := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
    Tate.AdelicFrame (X).actionObj.abelianScheme h (X).actionObj.action
      ((Global.FiniteAdeles ℚ) ⊗[ℚ] A) (t ≫ b))

omit [QuasiSeparatedSpace S] [QuasiSeparatedSpace T] in
private theorem fibreCoordinates_pullback
    {B : AbelianScheme S} {g m : ℕ} (v : FullLevel B g m) (a : Fin (2 * g) → ZMod m) :
    GroupScheme.Tate.levelBaseChange b B.toGrp (Over.mk t) m
      ((v.pullback b).fibreCoordinates Ω t a) = v.fibreCoordinates Ω (t ≫ b) a := by
  let e := GroupScheme.Tate.levelBaseChangeLinear B.toGrp b (Over.mk t) m
  have he : e.toLinearMap.comp ((v.pullback b).fibreCoordinates Ω t).toLinearMap =
      (v.fibreCoordinates Ω (t ≫ b)).toLinearMap := by
    apply (Pi.basisFun (ZMod m) (Fin (2 * g))).ext
    intro i
    rw [Pi.basisFun_apply]
    change e ((v.pullback b).fibreCoordinates Ω t (Pi.single i 1)) =
      v.fibreCoordinates Ω (t ≫ b) (Pi.single i 1)
    rw [FullLevel.fibreCoordinates_single, FullLevel.fibreCoordinates_single]
    exact fibreTuple_pullback b v.sections t i
  exact DFunLike.congr_fun he a

/-- The geometric lifting condition is reflected and preserved by pullback
with the original base-change comparisons for the action, dual and frame. -/
theorem harrisPrincipalFullLevelCondition_iff_baseChange
    (X : PObjS) (W : DualData X) (frameExists : FrameExists X)
    (m : Index (fun _ => True)) (v : FullLevel (BOf X) gH m.val) :
    (LiftAt t) (pullObj X W frameExists) m (v.pullback b) ↔ (LiftAt (t ≫ b)) X m v := by
  let e := frameBC X W
  let eLevel := GroupScheme.Tate.levelBaseChange b (BOf X).toGrp (Over.mk t) m.val
  constructor
  · rintro ⟨etaT, hnT, hvT⟩
    obtain ⟨eta, rfl⟩ := e.symm.surjective etaT
    have hn := (harrisIntegralFrameCondition_baseChange D C P dualityNaturality
      polarizationStability b compatibility h t X W frameExists eta).mp hnT
    refine ⟨eta, hn, fun a => ?_⟩
    have hr := harrisIntegralFrameReduction_baseChange D C P dualityNaturality
      polarizationStability b compatibility h t X W frameExists m eta hn hnT
        (harrisPrincipalSourceCoordinates D C h m a)
    have hc := (congrArg eLevel hr).trans (eLevel.apply_symm_apply _)
    exact hc.symm.trans ((congrArg eLevel (hvT a)).trans (fibreCoordinates_pullback b t v a))
  · rintro ⟨eta, hn, hv⟩
    have hnT := (harrisIntegralFrameCondition_baseChange D C P dualityNaturality
      polarizationStability b compatibility h t X W frameExists eta).mpr hn
    refine ⟨e.symm eta, hnT, fun a => ?_⟩
    have hr := harrisIntegralFrameReduction_baseChange D C P dualityNaturality
      polarizationStability b compatibility h t X W frameExists m eta hn hnT
        (harrisPrincipalSourceCoordinates D C h m a)
    exact (hr.trans (congrArg eLevel.symm (hv a))).trans
      ((congrArg eLevel.symm (fibreCoordinates_pullback b t v a).symm).trans
        (eLevel.symm_apply_apply _))

variable [ConnectedSpace S] [IsLocallyNoetherian S] [ConnectedSpace T] [IsLocallyNoetherian T]
  (ht : ∀ Y : Cover T, Finite (Fiber t Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T k.val).X.hom]
  [hμetT : ∀ k : Index (fun _ => True), Etale (mu T k.val).X.hom]

local notation "towerS" X:max =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.levelTower P.preservation P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability P.square P.universality compatibility h A
    (D.harrisHodgePELForm C) (t ≫ b) hs htor huS X
local notation "NormS" =>
  HarrisIntegralLevelCondition D C P compatibility h (t ≫ b) hs htor huS
local notation "pullLevel" => harrisIntegralNormalizedLevelBaseChange D C P dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT

/-- The ordered marking of a pulled-back normalized orbit is the ordinary
pullback of the original marking, on the same pulled-back abelian scheme. -/
theorem harrisPrincipalFullLevelEquiv_baseChange
    (X : PObjS) (W : DualData X) (frameExists : FrameExists X)
    (m : Index (fun _ => True)) (U : ULevel) (hU : U.toSubgroup = Cong m.val)
    (x : {x : (towerS X).obj U // NormS X U x}) :
    (harrisPrincipalFullLevelEquiv D C h P compatibility t ht htor huT
      (pullObj X W frameExists) m U hU (pullLevel X W frameExists U x)).val =
      (harrisPrincipalFullLevelEquiv D C h P compatibility (t ≫ b) hs htor huS
        X m U hU x).val.pullback b := by
  rw [harrisPrincipalFullLevelEquiv_apply_val, harrisPrincipalFullLevelEquiv_apply_val]
  apply fullLevel_eq_of_sections
  funext i
  let source := harrisPrincipalSourceCoordinates D C h m (Pi.single i 1)
  let e := GroupScheme.Tate.levelBaseChange b (BOf X).toGrp (Over.mk (𝟙 T)) m.val
  apply e.injective
  have he := harrisIntegralLevelSections_baseChange D C P dualityNaturality
    polarizationStability b compatibility h t ht hs htor huS huT X W frameExists
    m U hU.le x.val x.property source
  refine he.trans ?_
  let a : (Over.map b).obj (Over.mk (𝟙 T)) ⟶ Over.mk (𝟙 S) :=
    Over.homMk (𝟙 T ≫ b) (by simp)
  let a' : (Over.map b).obj (Over.mk (𝟙 T)) ⟶ Over.mk (𝟙 S) :=
    Over.homMk b (by simp)
  have haa' : a = a' := Over.OverMorphism.ext (Category.id_comp b)
  let z := harrisIntegralLevelSections D C P (t ≫ b) hs htor huS compatibility h
    X m U hU.le x.val x.property source
  change GroupScheme.Tate.levelRestrict (BOf X).toGrp a m.val z =
    e (e.symm (GroupScheme.Tate.levelRestrict (BOf X).toGrp a' m.val z))
  rw [haa', AddEquiv.apply_symm_apply]

end BaseChange

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
