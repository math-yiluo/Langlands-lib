import Langlands.Shimura.PEL.HarrisIntegralTateImages
import Langlands.AbelianScheme.Tate.WeilCompactOpenLevelTransport

/-! # Point independence of integral-normalized Harris levels -/

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
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
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
  {Ω Ω' Ω'' : Type} [Field Ω] [Field Ω'] [Field Ω'']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  {hr : ∀ Y : Cover S, Finite (Fiber r Y)}

local notation "PObj" => PositivePolarizedAction D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality (S := S)
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

omit [QuasiSeparatedSpace S] hμfin hμet in
private theorem fullImage_transport_iff (B : Langlands.AbelianScheme S)
    (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (z : Tate.Rational B (Over.mk s) (fun _ => True)) :
    (∃ x : GroupScheme.Tate.Full B.toGrp (Over.mk s),
      GroupScheme.Tate.toRational B.toGrp (Over.mk s) (fun _ => True) x = z) ↔
    (∃ y : GroupScheme.Tate.Full B.toGrp (Over.mk t),
      GroupScheme.Tate.toRational B.toGrp (Over.mk t) (fun _ => True) y =
        Tate.rationalTransport htor B (fun _ => True) hu path z) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Tate.integralTransport htor B (fun _ => True) hu path x,
      Tate.toRational_transport htor B (fun _ => True) hu path x⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := (Tate.integralTransport htor B (fun _ => True) hu path).surjective y
    refine ⟨x, (Tate.rationalTransport htor B (fun _ => True) hu path).injective ?_⟩
    exact (Tate.toRational_transport htor B (fun _ => True) hu path x).symm.trans hy

omit [IsScalarTower ℚ F A] in
/-- Actual geometric path transport preserves and reflects full integral normalization. -/
theorem harrisIntegralFrameCondition_point (X : PObj)
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) (eta : FrameAt X s) :
    (NormalizedAt t) X ((framePath X) path eta) ↔ (NormalizedAt s) X eta := by
  let := auxiliaryStarRing D C
  constructor
  · intro hn v
    exact (hn v).trans (fullImage_transport_iff htor hu X.actionObj.abelianScheme
      path (eta.1 v)).symm
  · intro hn v
    exact (hn v).trans (fullImage_transport_iff htor hu X.actionObj.abelianScheme
      path (eta.1 v))

local notation "Level" => FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)
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

omit [IsScalarTower ℚ F A] in
private theorem level_normalized_point (X : PObj)
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) (K : Level)
    (x : (towerAt X s hs).obj K) (hx : (LevelNormalizedAt s hs) X K x) :
    (LevelNormalizedAt t ht) X K ((levelPath X) K.toSubgroup path x) := by
  let := auxiliaryStarRing D C
  let := rightAt X s
  let := rightAt X t
  obtain ⟨eta, hn, heta⟩ := hx
  refine ⟨(framePath X) path eta,
    (harrisIntegralFrameCondition_point D C P compatibility h htor hu X path eta).mpr hn, ?_⟩
  change RightOrbit.mk K.toSubgroup ((framePath X) path eta) =
    RightOrbit.map K.toSubgroup ((framePath X) path)
      (fun _ _ => by apply Subtype.ext; ext v; rfl) x.val
  rw [← heta, RightOrbit.map_mk]

omit [IsScalarTower ℚ F A] in
/-- The original fixed-level point equivalence preserves and reflects normalization. -/
theorem harrisIntegralLevelCondition_point (X : PObj)
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) (K : Level)
    (x : (towerAt X s hs).obj K) :
    (LevelNormalizedAt t ht) X K ((levelPath X) K.toSubgroup path x) ↔
      (LevelNormalizedAt s hs) X K x := by
  let := auxiliaryStarRing D C
  constructor
  · intro hn
    have hb := level_normalized_point D C P compatibility h htor hu X path.symm K _ hn
    have heq := Tate.weilAdelicLevelTransport_symm P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability compatibility
      rationalWeilGeometricTransport X.hasDual X.geometry X.inversePoincare X.evaluation
      X.polarization h X.actionObj.action A (D.harrisHodgePELForm C) htor hu
      K.toSubgroup path
    rw [← heq, Equiv.symm_apply_apply] at hb
    exact hb
  · exact level_normalized_point D C P compatibility h htor hu X path K x

/-- Restrict the original fixed-orbit point comparison to normalized Harris levels. -/
def harrisIntegralNormalizedLevelPointEquiv (X : PObj)
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) (K : Level) :
    {x : (towerAt X s hs).obj K // (LevelNormalizedAt s hs) X K x} ≃
      {y : (towerAt X t ht).obj K // (LevelNormalizedAt t ht) X K y} :=
  ((levelPath X) K.toSubgroup path).subtypeEquiv
    (fun x => (harrisIntegralLevelCondition_point D C P compatibility h htor hu X path K x).symm)

local notation "normalizedPath" =>
  harrisIntegralNormalizedLevelPointEquiv D C P compatibility h htor hu

omit [IsScalarTower ℚ F A] in
@[simp] theorem harrisIntegralNormalizedLevelPointEquiv_val (X : PObj)
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) (K : Level)
    (x : {x : (towerAt X s hs).obj K // (LevelNormalizedAt s hs) X K x}) :
    ((normalizedPath X path K) x).val = (levelPath X) K.toSubgroup path x.val := rfl

omit [IsScalarTower ℚ F A] in
/-- Normalized fixed levels retain the canonical independence of the chosen path. -/
theorem harrisIntegralNormalizedLevelPointEquiv_path_independent (X : PObj)
    (path path' : fiberFunctor s hs ≅ fiberFunctor t ht) (K : Level) :
    normalizedPath X path K = normalizedPath X path' K := by
  let := auxiliaryStarRing D C
  apply Equiv.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun e => e x.val)
    (Tate.weilAdelicLevelTransport_path_independent P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability compatibility
      rationalWeilGeometricTransport X.hasDual X.geometry X.inversePoincare X.evaluation
      X.polarization h X.actionObj.action A (D.harrisHodgePELForm C) htor hu
      K.toSubgroup path path')


section Geometric

variable [ConnectedSpace S] [IsLocallyNoetherian S]
  [IsAlgClosed Ω] [IsAlgClosed Ω']

/-- Canonical comparison of normalized Harris fixed levels at geometric points. -/
def harrisIntegralNormalizedLevelGeometricEquiv (X : PObj) (K : Level) :
    {x : (towerAt X s hs).obj K // (LevelNormalizedAt s hs) X K x} ≃
      {y : (towerAt X t ht).obj K // (LevelNormalizedAt t ht) X K y} :=
  normalizedPath X (Classical.choice (geometricPathExists s t hs ht)) K

local notation "canonicalNormalized" =>
  harrisIntegralNormalizedLevelGeometricEquiv D C P compatibility h htor hu

omit [IsScalarTower ℚ F A] in
/-- Every geometric path computes the canonical normalized comparison. -/
theorem harrisIntegralNormalizedLevelGeometricEquiv_eq_path (X : PObj)
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) (K : Level) :
    canonicalNormalized X K = normalizedPath X path K :=
  harrisIntegralNormalizedLevelPointEquiv_path_independent
    D C P compatibility h htor hu X _ path K

local notation "canonicalTower" X:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicCompactOpenLevelGeometricTransport P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  compatibility (X).hasDual (X).geometry (X).inversePoincare (X).evaluation
  (X).polarization h (X).actionObj.action A (D.harrisHodgePELForm C) htor hu

omit [IsScalarTower ℚ F A] in
/-- Forgetting normalization gives the original canonical point comparison. -/
@[simp] theorem harrisIntegralNormalizedLevelGeometricEquiv_val (X : PObj) (K : Level)
    (x : {x : (towerAt X s hs).obj K // (LevelNormalizedAt s hs) X K x}) :
    ((canonicalNormalized X K) x).val =
      ((canonicalTower X) s t hs ht).hom.app K x.val := rfl

end Geometric

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
