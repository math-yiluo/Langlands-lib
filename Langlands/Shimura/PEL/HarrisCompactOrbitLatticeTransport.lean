import Langlands.Shimura.PEL.HarrisCompactOrbitLattice
import Langlands.Shimura.PEL.HarrisIntegralNormalizationBaseChange

/-! # Transport of compact orbit lattice normalization -/

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

local notation "Vf" => (Global.FiniteAdeles ℚ) ⊗[ℚ] A
local notation "Λf" => D.harrisHodgePELIntegralAdeleSpan C
local notation "G" => ScalarExtensionSimilitudes A A
  (Global.FiniteAdeles ℚ) (D.harrisHodgePELForm C)

variable (P : Prerequisites.{0})
  {S : Scheme.{0}} [QuasiSeparatedSpace S]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)

local notation "PObj" => PositivePolarizedAction D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality (S := S)
local notation "Frame" X:max =>
  letI := auxiliaryStarRing D C
  Tate.WeilAdelicFrame P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability (X).hasDual
  (X).geometry (X).inversePoincare (X).evaluation compatibility (X).polarization h
  (X).actionObj.action A (D.harrisHodgePELForm C) s
local notation "rightAction" X:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameRightAction P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  (X).hasDual (X).geometry (X).inversePoincare (X).evaluation compatibility (X).polarization
  h (X).actionObj.action A (D.harrisHodgePELForm C) s

/-- A chosen frame identifies the common source submodule and the integral Tate image. -/
def HarrisCompactFrameLatticeCondition (X : PObj) (K : Subgroup G) (eta : Frame X) : Prop :=
  letI := auxiliaryStarRing D C
  ∀ v : Vf, (∀ g : K, ∃ u : Vf, u ∈ Λf ∧ g.val.1.1 u = v) ↔
    ∃ x : GroupScheme.Tate.Full (X).actionObj.abelianScheme.toGrp (Over.mk s),
      GroupScheme.Tate.toRational (X).actionObj.abelianScheme.toGrp (Over.mk s)
        (fun _ => True) x = eta.1 v

local notation "Rat" X:max =>
  letI := auxiliaryStarRing D C
  Tate.Rational (X).actionObj.abelianScheme (Over.mk s) (fun _ => True)
local notation "frameLattice" => harrisCompactFrameLattice D C P compatibility h s

omit [IsScalarTower ℚ F A] in
private theorem frameLattice_apply_mem (X : PObj) (K : Subgroup G) (eta : Frame X) (v : Vf) :
    letI := auxiliaryStarRing D C
    eta.1 v ∈ frameLattice X K eta ↔ ∀ g : K, ∃ u : Vf, u ∈ Λf ∧ g.val.1.1 u = v := by
  let := auxiliaryStarRing D C
  let := rightAction X
  rw [mem_harrisCompactFrameLattice]
  apply forall_congr'
  intro g
  rw [mem_harrisIntegralFrameLattice]
  constructor
  · rintro ⟨u, hu, he⟩
    exact ⟨u, hu, eta.1.injective he⟩
  · rintro ⟨u, hu, he⟩
    exact ⟨u, hu, congrArg eta.1 he⟩

omit [IsScalarTower ℚ F A] in
/-- The condition on the source of the frame is equality of the carried
lattice with the actual full integral Tate image. -/
theorem harrisCompactFrameLatticeCondition_iff (X : PObj) (K : Subgroup G) (eta : Frame X) :
    letI := auxiliaryStarRing D C
    HarrisCompactFrameLatticeCondition D C P compatibility h s X K eta ↔
      (frameLattice X K eta : Set (Rat X)) = Set.range (GroupScheme.Tate.toRational
        X.actionObj.abelianScheme.toGrp (Over.mk s) (fun _ => True)) := by
  let := auxiliaryStarRing D C
  constructor
  · intro hn
    apply Set.ext
    intro w
    obtain ⟨v, rfl⟩ := eta.1.surjective w
    exact (frameLattice_apply_mem D C P compatibility h s X K eta v).trans (hn v)
  · intro he v
    exact (frameLattice_apply_mem D C P compatibility h s X K eta v).symm.trans
      (Set.ext_iff.mp he (eta.1 v))

section Point

variable {s}
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  {Ω' : Type} [Field Ω'] {t : Spec (.of Ω') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)} {ht : ∀ Y : Cover S, Finite (Fiber t Y)}

local notation "FrameAt" X:max a:max =>
  letI := auxiliaryStarRing D C
  Tate.WeilAdelicFrame P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability (X).hasDual
  (X).geometry (X).inversePoincare (X).evaluation compatibility (X).polarization h
  (X).actionObj.action A (D.harrisHodgePELForm C) a
local notation "rightAt" X:max a:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameRightAction P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability (X).hasDual (X).geometry
  (X).inversePoincare (X).evaluation compatibility (X).polarization h
  (X).actionObj.action A (D.harrisHodgePELForm C) a
local notation "RatAt" X:max a:max => letI := auxiliaryStarRing D C
  Tate.Rational (X).actionObj.abelianScheme (Over.mk a) (fun _ => True)
local notation "latAt" X:max a:max K:max z:max =>
  harrisCompactOrbitLattice D C P compatibility h a X K z
local notation "fullImage" X:max a:max => letI := auxiliaryStarRing D C
  Set.range (GroupScheme.Tate.toRational
  (X).actionObj.abelianScheme.toGrp (Over.mk a) (fun _ => True))
local notation "frameLatAt" X:max a:max K:max z:max =>
  harrisCompactFrameLattice D C P compatibility h a X K z

local notation "framePath" X:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameTransport P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability compatibility
  rationalWeilGeometricTransport (X).hasDual (X).geometry (X).inversePoincare
  (X).evaluation (X).polarization h (X).actionObj.action A
  (D.harrisHodgePELForm C) htor hu
local notation "levelPath" X:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicLevelTransport P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability compatibility
  rationalWeilGeometricTransport (X).hasDual (X).geometry (X).inversePoincare
  (X).evaluation (X).polarization h (X).actionObj.action A
  (D.harrisHodgePELForm C) htor hu
local notation "Level" => FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)
local notation "towerAt" X:max z:max hz:max =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.levelTower P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h A (D.harrisHodgePELForm C) z hz htor hu X
local notation "normAt" z:max => HarrisCompactFrameLatticeCondition D C P compatibility h z

omit [QuasiSeparatedSpace S] hμfin hμet in
private theorem fullImage_transport_mem_iff (B : Langlands.AbelianScheme S)
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
/-- Changing the geometric point preserves and reflects the source criterion. -/
theorem harrisCompactFrameLatticeCondition_point (X : PObj)
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) (K : Subgroup G) (eta : FrameAt X s) :
    (normAt t) X K ((framePath X) path eta) ↔ (normAt s) X K eta := by
  let := auxiliaryStarRing D C
  constructor
  · intro hn v
    exact (hn v).trans (fullImage_transport_mem_iff htor hu X.actionObj.abelianScheme
      path (eta.1 v)).symm
  · intro hn v
    exact (hn v).trans (fullImage_transport_mem_iff htor hu X.actionObj.abelianScheme
      path (eta.1 v))

omit [IsScalarTower ℚ F A] in
set_option maxHeartbeats 3200000 in
/-- Geometric point transport of a compact level orbit preserves and reflects
normalization by the full integral Tate image. -/
theorem harrisCompactOrbitLatticeCondition_point (X : PObj)
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) (K : Level) (x : (towerAt X s hs).obj K) :
    (latAt X t K.toSubgroup ((levelPath X) K.toSubgroup path x).val : Set (RatAt X t)) =
      fullImage X t ↔ (latAt X s K.toSubgroup x.val : Set (RatAt X s)) = fullImage X s := by
  let := auxiliaryStarRing D C
  let := rightAt X s
  let := rightAt X t
  let U := K.toSubgroup
  obtain ⟨eta, heta⟩ := Quotient.exists_rep x.val
  let f := (framePath X) path
  have hf : ∀ (eta : FrameAt X s) (g : G), f (right eta g) = right (f eta) g := by
    intro eta g
    apply Subtype.ext
    ext v
    rfl
  have heq : RightOrbit.mk U (f eta) = ((levelPath X) U path x).val :=
    congrArg (RightOrbit.map U f hf) heta
  change (latAt X t U ((levelPath X) U path x).val : Set (RatAt X t)) = fullImage X t ↔
    (latAt X s U x.val : Set (RatAt X s)) = fullImage X s
  rw [← heq, ← heta]
  change (frameLatAt X t U (f eta) : Set (RatAt X t)) = fullImage X t ↔
    (frameLatAt X s U eta : Set (RatAt X s)) = fullImage X s
  exact (harrisCompactFrameLatticeCondition_iff D C P compatibility h t X U (f eta)).symm.trans
    ((harrisCompactFrameLatticeCondition_point D C P compatibility h htor hu X path U eta).trans
      (harrisCompactFrameLatticeCondition_iff D C P compatibility h s X U eta))

end Point

section BaseChange

variable (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  {T : Scheme.{0}} (b : T ⟶ S) [QuasiSeparatedSpace T]
  {Ξ : Type} [Field Ξ] (t : Spec (.of Ξ) ⟶ T)

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
  HarrisCompactFrameLatticeCondition D C P compatibility h s₀
local notation "FrameExists" X:max =>
  Nonempty (letI := auxiliaryStarRing D C
    letI := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
    Tate.AdelicFrame (X).actionObj.abelianScheme h (X).actionObj.action
      ((Global.FiniteAdeles ℚ) ⊗[ℚ] A) (t ≫ b))

omit [QuasiSeparatedSpace S] [QuasiSeparatedSpace T] in
private theorem fullImage_baseChange_mem_iff (B : Langlands.AbelianScheme S)
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

omit [IsScalarTower ℚ F A] in
/-- Pointed base change identifies the source criteria of the two frames. -/
theorem harrisCompactFrameLatticeCondition_baseChange (X : PObj) (W : DualData X)
    (frameExists : FrameExists X) (K : Subgroup G)
    (eta : FrameAt X (t ≫ b)) :
    (NormalizedAt t) (pullObj X W frameExists) K ((frameBC X W).symm eta) ↔
      (NormalizedAt (t ≫ b)) X K eta := by
  let := auxiliaryStarRing D C
  constructor
  · intro hn v
    have hb := fullImage_baseChange_mem_iff b t X.actionObj.abelianScheme
      (((frameBC X W).symm eta).1 v)
    simp only [Tate.weilAdelicFrameBaseChange_symm_apply, LinearEquiv.apply_symm_apply] at hb
    exact (hn v).trans hb
  · intro hn v
    have hb := fullImage_baseChange_mem_iff b t X.actionObj.abelianScheme
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

local notation "RatAt" X:max a:max => letI := auxiliaryStarRing D C
  Tate.Rational (X).actionObj.abelianScheme (Over.mk a) (fun _ => True)
local notation "latAt" X:max a:max K:max z:max =>
  harrisCompactOrbitLattice D C P compatibility h a X K z
local notation "fullImage" X:max a:max => letI := auxiliaryStarRing D C
  Set.range (GroupScheme.Tate.toRational
  (X).actionObj.abelianScheme.toGrp (Over.mk a) (fun _ => True))
local notation "frameLatAt" X:max a:max K:max z:max =>
  harrisCompactFrameLattice D C P compatibility h a X K z

omit [IsScalarTower ℚ F A] in
set_option maxHeartbeats 3200000 in
/-- Pointed base change on fixed compact level orbits preserves and reflects
normalization by the full integral Tate image. -/
theorem harrisCompactOrbitLatticeCondition_baseChange (X : PObj) (W : DualData X)
    (frameExists : FrameExists X) (K : Level) (x : (towerAt X (t ≫ b) hs huS).obj K) :
    let Y := pullObj X W frameExists
    ((latAt Y t K.toSubgroup ((levelBC X W) K.toSubgroup x).val : Set (RatAt Y t)) = fullImage Y t) ↔
      (latAt X (t ≫ b) K.toSubgroup x.val : Set (RatAt X (t ≫ b))) = fullImage X (t ≫ b) := by
  let := auxiliaryStarRing D C
  let Y := pullObj X W frameExists
  let := rightAt X (t ≫ b)
  let := rightAt Y t
  let U := K.toSubgroup
  obtain ⟨eta, heta⟩ := Quotient.exists_rep x.val
  let xi := (frameBC X W).symm eta
  have heq : RightOrbit.mk U xi = ((levelBC X W) U x).val := by
    exact congrArg ((orbitBC X W) U).symm heta
  change (latAt Y t U ((levelBC X W) U x).val : Set (RatAt Y t)) = fullImage Y t ↔
    (latAt X (t ≫ b) U x.val : Set (RatAt X (t ≫ b))) = fullImage X (t ≫ b)
  rw [← heq, ← heta]
  change (frameLatAt Y t U xi : Set (RatAt Y t)) = fullImage Y t ↔
    (frameLatAt X (t ≫ b) U eta : Set (RatAt X (t ≫ b))) = fullImage X (t ≫ b)
  exact (harrisCompactFrameLatticeCondition_iff D C P compatibility h t Y U xi).symm.trans
    ((harrisCompactFrameLatticeCondition_baseChange D C P compatibility h dualityNaturality
      polarizationStability b t X W frameExists U eta).trans
      (harrisCompactFrameLatticeCondition_iff D C P compatibility h (t ≫ b) X U eta))

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

omit [IsScalarTower ℚ F A] in
set_option maxHeartbeats 1600000 in
/-- The actual Harris representative pullback preserves and reflects compact
orbit lattice normalization. -/
theorem harrisCompactOrbitLatticeCondition_levelDataBaseChange
    (dualData : ∀ X : PObj, DualData X) (U : HarrisLevel D) (x : DataS U) :
    let y := (pullData dualData) U x
    let K := (hodgeLevelFunctor D C).obj U
    (latAt y.1 t K.toSubgroup y.2.val : Set (RatAt y.1 t)) = fullImage y.1 t ↔
      (latAt x.1 (t ≫ b) K.toSubgroup x.2.val : Set (RatAt x.1 (t ≫ b))) = fullImage x.1 (t ≫ b) := by
  let := auxiliaryStarRing D C
  let W := dualData x.1
  let frameExists := level_nonempty_adelicFrame D C P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
    P.universality b compatibility h t hs htor huS x.1 U x.2
  exact harrisCompactOrbitLatticeCondition_baseChange D C P compatibility h dualityNaturality
    polarizationStability b t ht hs htor huS huT x.1 W
    frameExists ((hodgeLevelFunctor D C).obj U) x.2

end BaseChange

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
