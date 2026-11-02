import Langlands.Shimura.PEL.HarrisTaylorCMIntegralClassImage
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedPointTransport

/-! # Point independence of the exact integral-action CM class image -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  {S : Scheme.{0}} (p : S ⟶ Spec (.of F))
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω Ω' Ω'' : Type} [Field Ω] [Field Ω'] [Field Ω'']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  {hr : ∀ Y : Cover S, Finite (Fiber r Y)}
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [QuasiSeparatedSpace S]
  (additivity : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))

local notation "RepAt" => IntegralCMRepresentative D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h
local notation "repClassAt" => integralCMRepresentativeClass D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h
local notation "ConditionAt" => IntegralCMClassCondition D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h
local notation "ImageAt" => IntegralCMClassImage D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h
local notation "imageTowerAt" => integralCMClassImageTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h
local notation "moveData" => HarrisTaylorLieWeilLevel.pointMapRepresentative D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor hu
local notation "moveClass" => classPointMap D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h
  htor hu additivity
local notation "moveTower" => classPointTowerIso D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h
  htor hu additivity

/-- Change only the point presentation of the invariant orbit, retaining the integral action. -/
def integralCMRepresentativePointMap (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : HarrisLevel D) (x : RepAt s hs htor hu U) : RepAt t ht htor hu U := by
  let := auxiliaryStarRing D C
  exact ⟨moveData path U x.data, x.condition, x.restriction⟩

local notation "moveRep" => integralCMRepresentativePointMap D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h htor hu

/-- The supplied integral-action representative maps to its original CM point comparison. -/
@[simp] theorem integralCMRepresentativeClass_pointMap
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) (U : HarrisLevel D)
    (x : RepAt s hs htor hu U) :
    repClassAt t ht htor hu additivity (moveRep path U x) =
      moveClass path U (repClassAt s hs htor hu additivity x) := rfl

/-- Having an integral-action representative is preserved by the actual point comparison. -/
theorem integralCMClassCondition_pointMap (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : HarrisLevel D)
    (q : (HarrisNumericalWeilLevel.isoClassTower D C
      (isCMSection_harrisCMSection E (algebraMap L F) τ₀) preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      (D.harrisTaylorReflexStructure C p) compatibility h s hs htor hu additivity L p).obj U)
    (hq : ConditionAt s hs htor hu additivity q) :
    ConditionAt t ht htor hu additivity (moveClass path U q) := by
  obtain ⟨x, hx⟩ := hq
  refine ⟨moveRep path U x, ?_⟩
  rw [integralCMRepresentativeClass_pointMap]
  exact congrArg (moveClass path U) hx

/-- Restrict the actual CM point map to its exact integral-action image. -/
def integralCMClassImagePointMap (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : HarrisLevel D) (q : ImageAt s hs htor hu additivity U) :
    ImageAt t ht htor hu additivity U :=
  ⟨moveClass path U q.val,
    integralCMClassCondition_pointMap D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality p compatibility h
      htor hu additivity path U q.val q.property⟩

local notation "moveImage" => integralCMClassImagePointMap D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h htor hu additivity

/-- Reversing the path gives the inverse on the exact integral-action class image. -/
def integralCMClassImagePointEquiv (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : HarrisLevel D) :
    ImageAt s hs htor hu additivity U ≃ ImageAt t ht htor hu additivity U where
  toFun := moveImage path U
  invFun := moveImage path.symm U
  left_inv q := by
    apply Subtype.ext
    exact (classPointEquiv D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p compatibility h htor hu
      additivity path U).left_inv q.val
  right_inv q := by
    apply Subtype.ext
    exact (classPointEquiv D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p compatibility h htor hu
      additivity path U).right_inv q.val

/-- Point comparison on the integral image is natural for every original level transporter. -/
def integralCMClassImagePointTowerIso (path : fiberFunctor s hs ≅ fiberFunctor t ht) :
    imageTowerAt s hs htor hu additivity ≅ imageTowerAt t ht htor hu additivity :=
  NatIso.ofComponents (fun U => (integralCMClassImagePointEquiv D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    p compatibility h htor hu additivity path U).toIso) (by
      intro U V f
      ext q
      apply Subtype.ext
      exact (moveTower path).hom.naturality_apply f q.val)

local notation "moveImageTower" => integralCMClassImagePointTowerIso D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  p compatibility h htor hu additivity

/-- The comparison is the restriction of the original normalized CM comparison. -/
theorem integralCMClassImagePointTowerIso_inclusion
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (moveImageTower path).hom ≫
      integralCMClassImageInclusion D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality p compatibility h t ht htor hu additivity =
    integralCMClassImageInclusion D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p compatibility h s hs htor hu additivity ≫
        (moveTower path).hom := rfl

/-- Independence holds for the actual image, not merely after forgetting the level. -/
theorem integralCMClassImagePointTowerIso_path_independent
    (path path2 : fiberFunctor s hs ≅ fiberFunctor t ht) :
    moveImageTower path = moveImageTower path2 := by
  apply Iso.ext
  ext U q
  apply Subtype.ext
  exact congrArg (fun k => k.hom.app U q.val)
    (classPointTowerIso_path_independent D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality p compatibility h
      htor hu additivity path path2)

@[simp] theorem integralCMClassImagePointTowerIso_refl :
    moveImageTower (Iso.refl (fiberFunctor s hs)) =
      Iso.refl (imageTowerAt s hs htor hu additivity) := by
  apply Iso.ext
  ext U q
  apply Subtype.ext
  exact congrArg (fun k => k.hom.app U q.val)
    (classPointTowerIso_refl D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p compatibility h htor hu
      additivity (s := s) (hs := hs))

theorem integralCMClassImagePointTowerIso_trans
    (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (path2 : fiberFunctor t ht ≅ fiberFunctor r hr) :
    moveImageTower (path ≪≫ path2) = moveImageTower path ≪≫ moveImageTower path2 := by
  apply Iso.ext
  ext U q
  apply Subtype.ext
  exact congrArg (fun k => k.hom.app U q.val)
    (classPointTowerIso_trans D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p compatibility h htor hu
      additivity path path2)

theorem integralCMClassImagePointTowerIso_symm
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (moveImageTower path).symm = moveImageTower path.symm := by
  apply Iso.ext
  ext U q
  rfl

section Geometric
variable [ConnectedSpace S] [IsLocallyNoetherian S]

/-- Canonical geometric-point comparison of the exact integral-action class images. -/
def integralCMClassImageGeometricPointTowerIso
    {Ωa Ωb : Type} [Field Ωa] [IsAlgClosed Ωa] [Field Ωb] [IsAlgClosed Ωb]
    (a : Spec (.of Ωa) ⟶ S) (b : Spec (.of Ωb) ⟶ S)
    (ha : ∀ Y : Cover S, Finite (Fiber a Y)) (hb : ∀ Y : Cover S, Finite (Fiber b Y)) :
    imageTowerAt a ha htor hu additivity ≅ imageTowerAt b hb htor hu additivity :=
  moveImageTower (Classical.choice (geometricPathExists a b ha hb))

local notation "geometricMove" => integralCMClassImageGeometricPointTowerIso D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  p compatibility h htor hu additivity

variable [IsAlgClosed Ω] [IsAlgClosed Ω'] [IsAlgClosed Ω'']

theorem integralCMClassImageGeometricPointTowerIso_eq_path
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) :
    geometricMove s t hs ht = moveImageTower path :=
  integralCMClassImagePointTowerIso_path_independent D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality p
    compatibility h htor hu additivity _ path

@[simp] theorem integralCMClassImageGeometricPointTowerIso_refl :
    geometricMove s s hs hs = Iso.refl (imageTowerAt s hs htor hu additivity) := by
  rw [integralCMClassImageGeometricPointTowerIso_eq_path D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality p
    compatibility h htor hu additivity (Iso.refl (fiberFunctor s hs))]
  exact integralCMClassImagePointTowerIso_refl D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality p compatibility h
    htor hu additivity

theorem integralCMClassImageGeometricPointTowerIso_trans :
    geometricMove s r hs hr = geometricMove s t hs ht ≪≫ geometricMove t r ht hr := by
  let path := Classical.choice (geometricPathExists s t hs ht)
  let path2 := Classical.choice (geometricPathExists t r ht hr)
  rw [integralCMClassImageGeometricPointTowerIso_eq_path D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality p
      compatibility h htor hu additivity (path ≪≫ path2),
    integralCMClassImageGeometricPointTowerIso_eq_path D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality p
      compatibility h htor hu additivity path,
    integralCMClassImageGeometricPointTowerIso_eq_path D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality p
      compatibility h htor hu additivity path2]
  exact integralCMClassImagePointTowerIso_trans D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality p compatibility h
    htor hu additivity path path2

theorem integralCMClassImageGeometricPointTowerIso_symm :
    (geometricMove s t hs ht).symm = geometricMove t s ht hs := by
  let path := Classical.choice (geometricPathExists s t hs ht)
  rw [integralCMClassImageGeometricPointTowerIso_eq_path D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality p
      compatibility h htor hu additivity path,
    integralCMClassImageGeometricPointTowerIso_eq_path D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality p
      compatibility h htor hu additivity path.symm]
  exact integralCMClassImagePointTowerIso_symm D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality p compatibility h
    htor hu additivity path

end Geometric
end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
