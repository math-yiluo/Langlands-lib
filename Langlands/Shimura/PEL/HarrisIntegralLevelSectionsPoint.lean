import Langlands.Shimura.PEL.HarrisIntegralOrderedFullLevel
import Langlands.Shimura.PEL.HarrisIntegralNormalizationPointComparison

/-! # Independence of the reference point for Harris level sections -/

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
  {S : Scheme.{0}} [QuasiSeparatedSpace S]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  {Ω Ω' : Type} [Field Ω] [Field Ω']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}

local notation "PObj" =>
  letI := auxiliaryStarRing D C
  PositivePolarizedAction D C P.preservation P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability P.square P.universality (S := S)
local notation:max "BOf" X:max =>
  letI := auxiliaryStarRing D C
  (X).actionObj.abelianScheme
local notation "FrameAt" X:max s₀:max =>
  letI := auxiliaryStarRing D C
  Tate.WeilAdelicFrame P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability (X).hasDual
  (X).geometry (X).inversePoincare (X).evaluation compatibility (X).polarization h
  (X).actionObj.action A (D.harrisHodgePELForm C) s₀
local notation "rightAt" X:max s₀:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameRightAction P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability (X).hasDual
  (X).geometry (X).inversePoincare (X).evaluation compatibility (X).polarization
  h (X).actionObj.action A (D.harrisHodgePELForm C) s₀
local notation "framePath" X:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameTransport P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability compatibility
  rationalWeilGeometricTransport (X).hasDual (X).geometry (X).inversePoincare
  (X).evaluation (X).polarization h (X).actionObj.action A
  (D.harrisHodgePELForm C) htor hu
local notation "NormalizedAt" s₀:max =>
  HarrisIntegralFrameCondition D C P compatibility h s₀
local notation:max "redAt" X:max s₀:max =>
  harrisIntegralFrameReduction D C P compatibility h s₀ X
local notation:max "fullAt" X:max s₀:max =>
  harrisIntegralFrameFull D C P compatibility h s₀ X

/-- Reduction of a transported normalized frame is finite-level path transport
of the original reduction. -/
theorem harrisIntegralFrameReduction_point (X : PObj)
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) (m : Index (fun _ => True))
    (eta : FrameAt X s) (hn : (NormalizedAt s) X eta) :
    ∀ (hn' : (NormalizedAt t) X ((framePath X) path eta))
      (q : HarrisIntegralSourceMod D C m.val),
      (redAt X t) m ((framePath X) path eta) hn' q =
        Tate.levelTransport htor (BOf X) m.val m.property.1 (hu m) path
          ((redAt X s) m eta hn q) := by
  let := auxiliaryStarRing D C
  intro hn' q
  obtain ⟨v, rfl⟩ := (harrisIntegralSourceMultiples D C m.val).mkQ_surjective q
  rw [harrisIntegralFrameReduction_mkQ, harrisIntegralFrameReduction_mkQ]
  have hf : (fullAt X t) ((framePath X) path eta) hn' v =
      Tate.integralTransport htor (BOf X) (fun _ => True) hu path ((fullAt X s) eta hn v) := by
    apply GroupScheme.Tate.full_toRational_injective (BOf X).toGrp (Over.mk t)
    rw [Tate.toRational_transport, harrisIntegralFrameFull_toRational,
      harrisIntegralFrameFull_toRational]
    rfl
  rw [hf]
  rfl

omit [QuasiSeparatedSpace S] hμfin hμet in
/-- Path transport on finite torsion carries the value of a global torsion section
at the first geometric point to its value at the second. -/
theorem levelTransport_levelRestrict_global (B : AbelianScheme S)
    (m : Index (fun _ => True)) (hm : IsUnit (m.val : Γ(S, ⊤)))
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (v : GroupScheme.Tate.Level B.toGrp (Over.mk (𝟙 S)) m.val) :
    Tate.levelTransport htor B m.val m.property.1 hm p
        (GroupScheme.Tate.levelRestrict B.toGrp
          (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) m.val v) =
      GroupScheme.Tate.levelRestrict B.toGrp
        (Over.homMk t (by simp) : Over.mk t ⟶ Over.mk (𝟙 S)) m.val v := by
  let Y : Cover S := cover (𝟙 S)
  let Z : Cover S := Tate.torsionCover htor B m.val m.property.1 hm
  let a : Fiber s Y := (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S))
  let b : Fiber t Y := (Over.homMk t (by simp) : Over.mk t ⟶ Over.mk (𝟙 S))
  let k := GroupScheme.Tate.kernelLevelEquiv B.toGrp (Over.mk (𝟙 S)) m.val
  obtain ⟨w, rfl⟩ := k.surjective v
  let f : Y ⟶ Z := ObjectProperty.homMk w.toMul
  have hb : p.hom.app Y a = b := Over.OverMorphism.ext (by
    change (p.hom.app Y a : Fiber t Y).left = t
    have hw := (show Fiber t Y from p.hom.app Y a).w
    change (p.hom.app Y a : Fiber t Y).left ≫ 𝟙 S = t at hw
    exact (Category.comp_id _).symm.trans hw)
  have hp : p.hom.app Z (a ≫ f.hom) = b ≫ f.hom :=
    (ConcreteCategory.congr_hom (p.hom.naturality f) a).trans
      (congrArg (fun x : Fiber t Y => x ≫ f.hom) hb)
  rw [GroupScheme.Tate.levelRestrict_kernelLevelEquiv,
    GroupScheme.Tate.levelRestrict_kernelLevelEquiv, Tate.levelTransport_kernel]
  exact congrArg (fun x : Fiber t Z => GroupScheme.Tate.kernelLevelEquiv B.toGrp (Over.mk t)
    m.val (Additive.ofMul x)) hp

local notation "ULevel" => FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)
local notation "Cong" => harrisIntegralAdeleCongruence D C
local notation "towerAt" X:max s₀:max hs₀:max =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.levelTower P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h A (D.harrisHodgePELForm C) s₀ hs₀ htor hu X
local notation "LevelNormalizedAt" s₀:max hs₀:max =>
  HarrisIntegralLevelCondition D C P compatibility h s₀ hs₀ htor hu
local notation "levelPath" X:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicLevelTransport P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability compatibility
  rationalWeilGeometricTransport (X).hasDual (X).geometry (X).inversePoincare
  (X).evaluation (X).polarization h (X).actionObj.action A
  (D.harrisHodgePELForm C) htor hu

section Geometric

variable [ConnectedSpace S] [IsLocallyNoetherian S] [IsAlgClosed Ω] [IsAlgClosed Ω']

/-- The actual global torsion sections attached to a normalized invariant orbit do
not depend on the geometric reference point: transporting the orbit to another
geometric point gives the same global sections. -/
theorem harrisIntegralLevelSections_point (X : PObj)
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) (m : Index (fun _ => True))
    (U : ULevel) (hU : U.toSubgroup ≤ Cong m.val) (x : (towerAt X s hs).obj U)
    (hx : (LevelNormalizedAt s hs) X U x) (q : HarrisIntegralSourceMod D C m.val) :
    harrisIntegralLevelSections D C P t ht htor hu compatibility h X m U hU
        ((levelPath X) U.toSubgroup path x)
        ((harrisIntegralLevelCondition_point D C P compatibility h htor hu X path U x).mpr hx)
        q =
      harrisIntegralLevelSections D C P s hs htor hu compatibility h X m U hU x hx q := by
  let := auxiliaryStarRing D C
  let _ := rightAt X s
  let _ := rightAt X t
  obtain ⟨eta, hn, heta⟩ := id hx
  have hn' := (harrisIntegralFrameCondition_point D C P compatibility h htor hu X path eta).mpr hn
  have heta' : RightOrbit.mk U.toSubgroup ((framePath X) path eta) =
      ((levelPath X) U.toSubgroup path x).val := by
    change RightOrbit.mk U.toSubgroup ((framePath X) path eta) =
      RightOrbit.map U.toSubgroup ((framePath X) path)
        (fun _ _ => by apply Subtype.ext; ext v; rfl) x.val
    rw [← heta, RightOrbit.map_mk]
  apply (harrisIntegralGlobalTorsionEquiv D C P t ht htor hu X m).injective
  apply Subtype.ext
  rw [harrisIntegralGlobalTorsionEquiv_apply, harrisIntegralGlobalTorsionEquiv_apply]
  refine (harrisIntegralLevelSections_restrict D C P t ht htor hu compatibility h X m U hU
    _ _ q).trans ?_
  refine (harrisIntegralLevelReduction_apply D C P compatibility h t ht htor hu X m U hU
    _ _ ((framePath X) path eta) hn' heta' q).trans ?_
  refine (harrisIntegralFrameReduction_point D C P compatibility h htor hu X path m
    eta hn hn' q).trans ?_
  rw [← harrisIntegralLevelReduction_apply D C P compatibility h s hs htor hu X m U hU x hx
    eta hn heta q, ← harrisIntegralLevelSections_restrict D C P s hs htor hu compatibility h
    X m U hU x hx q]
  exact levelTransport_levelRestrict_global htor (BOf X) m (hu m) path _

variable [IsScalarTower ℚ F A] [IsScalarTower ℚ E F]

/-- The ordered full finite level of a normalized invariant orbit has the same
global ordered sections when the orbit is transported to another geometric point. -/
theorem harrisIntegralOrderedFullLevel_point (X : PObj)
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) (m : Index (fun _ => True))
    (U : ULevel) (hU : U.toSubgroup ≤ Cong m.val) (x : (towerAt X s hs).obj U)
    (hx : (LevelNormalizedAt s hs) X U x) :
    (harrisIntegralOrderedFullLevel D C P compatibility h t ht htor hu X m U hU
        ((levelPath X) U.toSubgroup path x)
        ((harrisIntegralLevelCondition_point D C P compatibility h htor hu X path U x).mpr
          hx)).sections =
      (harrisIntegralOrderedFullLevel D C P compatibility h s hs htor hu X m U hU x hx).sections := by
  funext i
  exact harrisIntegralLevelSections_point D C P compatibility h htor hu X path m U hU x hx _

/-- The ordered sections are invariant under the published transport of normalized orbits,
`harrisIntegralNormalizedLevelPointEquiv`. -/
theorem harrisIntegralOrderedFullLevel_normalizedTransport (X : PObj)
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) (m : Index (fun _ => True))
    (U : ULevel) (hU : U.toSubgroup ≤ Cong m.val)
    (x : {x : (towerAt X s hs).obj U // (LevelNormalizedAt s hs) X U x}) :
    (harrisIntegralOrderedFullLevel D C P compatibility h t ht htor hu X m U hU
        (harrisIntegralNormalizedLevelPointEquiv D C P compatibility h htor hu X path U x).val
        (harrisIntegralNormalizedLevelPointEquiv D C P compatibility h htor hu X path U
          x).property).sections =
      (harrisIntegralOrderedFullLevel D C P compatibility h s hs htor hu X m U hU x.val
        x.property).sections :=
  harrisIntegralOrderedFullLevel_point D C P compatibility h htor hu X path m U hU x.val
    x.property

end Geometric

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
