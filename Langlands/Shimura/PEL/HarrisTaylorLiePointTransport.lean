import Langlands.Shimura.PEL.HarrisTaylorLieWeilTower
import Langlands.Shimura.PEL.PolarizedWeilLevelPointTransport

/-! # Point independence of the actual Harris dimension and positive Lie tower -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorLieWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
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
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  {S : Scheme.{0}}
  (L : Type) [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  (p : S ⟶ Spec (.of F))

variable
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

local notation "Level" => HarrisLevel D
local notation "indexFunctor" => hodgeLevelFunctor D C
local notation "dataAt" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
local notation "Good" => ObjectCondition D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
local notation "ambientAt" => AmbientClass D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
local notation "ambientMkAt" => ambientClassOf D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
local notation "conditionAt" => ClassCondition D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p compatibility h
local notation "classesAt" => IsoClass D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p compatibility h
local notation "mkAt" => classOf D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p compatibility h
local notation "ambientTowerAt" => ambientTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
local notation "towerAt" => isoClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p compatibility h
local notation "inclusionAt" => inclusionNatTrans D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p compatibility h
local notation "forgetJointAt" => forgetDimensionLieAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality L p compatibility h
local notation "forgetJointTowerAt" => forgetDimensionLieActionNatTrans D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality L p
  compatibility h

/-- Change the point presentation of the actual orbit, retaining the identical polarized object. -/
def pointMapRepresentative (path : fiberFunctor s hs ≅ fiberFunctor t ht) (U : Level)
    (x : dataAt s hs htor hu U) : dataAt t ht htor hu U := by
  letI := auxiliaryStarRing D C
  exact PolarizedWeilLevel.pointMapData preservation composition unitCoherence associativity
    comparison symmetry stability square universality compatibility h A
    (D.harrisHodgePELForm C) htor hu path ((indexFunctor).obj U) x

local notation "moveRep" => pointMapRepresentative D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor hu

@[simp] theorem pointMapRepresentative_fst (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : Level) (x : dataAt s hs htor hu U) : (moveRep path U x).1 = x.1 := rfl

/-- The dimension and positive Lie conditions still hold on that very same representative. -/
@[simp] theorem objectCondition_pointMapRepresentative_iff
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) (U : Level) (x : dataAt s hs htor hu U) :
    Good (moveRep path U x).1 ↔ Good x.1 := Iff.rfl

/-- Reindex actual polarized point transport by the original opposite Harris level group. -/
def ambientPointTowerIso (path : fiberFunctor s hs ≅ fiberFunctor t ht) :
    ambientTowerAt s hs htor hu additivity ≅ ambientTowerAt t ht htor hu additivity := by
  letI := auxiliaryStarRing D C
  exact Functor.isoWhiskerLeft indexFunctor
    (PolarizedWeilLevel.classPointTowerIso preservation composition unitCoherence associativity
      comparison symmetry stability square universality compatibility h A
      (D.harrisHodgePELForm C) htor hu additivity path)

local notation "moveAmbient" => ambientPointTowerIso D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor hu additivity

@[simp] theorem ambientPointTowerIso_classOf (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : Level) (x : dataAt s hs htor hu U) :
    (moveAmbient path).hom.app U (ambientMkAt s hs htor hu additivity x) =
      ambientMkAt t ht htor hu additivity (moveRep path U x) := rfl

/-- Carry one joint satisfying representative through the actual point comparison. -/
theorem classCondition_pointMap (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : Level) (q : ambientAt s hs htor hu additivity U)
    (hq : conditionAt s hs htor hu additivity q) :
    conditionAt t ht htor hu additivity ((moveAmbient path).hom.app U q) := by
  obtain ⟨x, hx, hgood⟩ := hq
  refine ⟨moveRep path U x, ?_, hgood⟩
  rw [← hx]
  rfl

/-- Restrict the actual polarized quotient transport to the joint dimension-and-Lie image. -/
def classPointMap (path : fiberFunctor s hs ≅ fiberFunctor t ht) (U : Level)
    (q : classesAt s hs htor hu additivity U) : classesAt t ht htor hu additivity U :=
  ⟨(moveAmbient path).hom.app U q.val,
    classCondition_pointMap D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality L p compatibility h htor hu
      additivity path U q.val q.property⟩

local notation "moveClass" => classPointMap D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p compatibility h htor hu additivity

@[simp] theorem classPointMap_val (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : Level) (q : classesAt s hs htor hu additivity U) :
    (moveClass path U q).val = (moveAmbient path).hom.app U q.val := rfl

@[simp] theorem classPointMap_classOf (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : Level) (x : dataAt s hs htor hu U) (hx : Good x.1) :
    moveClass path U (mkAt s hs htor hu additivity x hx) =
      mkAt t ht htor hu additivity (moveRep path U x) hx := rfl

/-- Reverse paths supply the inverse of the restricted actual class map. -/
def classPointEquiv (path : fiberFunctor s hs ≅ fiberFunctor t ht) (U : Level) :
    classesAt s hs htor hu additivity U ≃ classesAt t ht htor hu additivity U where
  toFun := moveClass path U
  invFun := moveClass path.symm U
  left_inv q := by
    let := auxiliaryStarRing D C
    apply Subtype.ext
    exact (PolarizedWeilLevel.classPointEquiv preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h A
      (D.harrisHodgePELForm C) htor hu additivity path ((indexFunctor).obj U)).left_inv q.val
  right_inv q := by
    let := auxiliaryStarRing D C
    apply Subtype.ext
    exact (PolarizedWeilLevel.classPointEquiv preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h A
      (D.harrisHodgePELForm C) htor hu additivity path ((indexFunctor).obj U)).right_inv q.val

/-- Point comparison commutes with all original Harris transporters, including both Hecke legs. -/
def classPointTowerIso (path : fiberFunctor s hs ≅ fiberFunctor t ht) :
    towerAt s hs htor hu additivity ≅ towerAt t ht htor hu additivity :=
  NatIso.ofComponents (fun U => (classPointEquiv D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality L p compatibility h
    htor hu additivity path U).toIso) (by
      intro U V f
      ext q
      apply Subtype.ext
      exact (moveAmbient path).hom.naturality_apply f q.val)

local notation "moveTower" => classPointTowerIso D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p compatibility h htor hu additivity

@[simp] theorem classPointTowerIso_hom_app (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : Level) (q : classesAt s hs htor hu additivity U) :
    (moveTower path).hom.app U q = moveClass path U q := rfl

@[simp] theorem classPointTowerIso_inv_app (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : Level) (q : classesAt t ht htor hu additivity U) :
    (moveTower path).inv.app U q = moveClass path.symm U q := rfl

theorem classPointTowerIso_path_independent (path path2 : fiberFunctor s hs ≅ fiberFunctor t ht) :
    moveTower path = moveTower path2 := by
  let := auxiliaryStarRing D C
  apply Iso.ext
  ext U q
  apply Subtype.ext
  exact congrFun (PolarizedWeilLevel.classPointMap_path_independent preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h A (D.harrisHodgePELForm C) htor hu additivity path path2 ((indexFunctor).obj U)) q.val

@[simp] theorem classPointTowerIso_refl :
    moveTower (Iso.refl (fiberFunctor s hs)) = Iso.refl (towerAt s hs htor hu additivity) := by
  let := auxiliaryStarRing D C
  apply Iso.ext
  ext U q
  apply Subtype.ext
  exact PolarizedWeilLevel.classPointMap_refl preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h A
    (D.harrisHodgePELForm C) htor hu additivity ((indexFunctor).obj U) q.val

theorem classPointTowerIso_trans (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (path2 : fiberFunctor t ht ≅ fiberFunctor r hr) :
    moveTower (path ≪≫ path2) = moveTower path ≪≫ moveTower path2 := by
  let := auxiliaryStarRing D C
  apply Iso.ext
  ext U q
  apply Subtype.ext
  exact PolarizedWeilLevel.classPointMap_trans preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h A
    (D.harrisHodgePELForm C) htor hu additivity path path2 ((indexFunctor).obj U) q.val

theorem classPointTowerIso_symm (path : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (moveTower path).symm = moveTower path.symm := by
  apply Iso.ext
  ext U q
  rfl

/-- Inclusion into the actual ambient polarized tower commutes with point comparison. -/
theorem inclusionNatTrans_classPointTowerIso (path : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (moveTower path).hom ≫ inclusionAt t ht htor hu additivity =
      inclusionAt s hs htor hu additivity ≫ (moveAmbient path).hom := rfl

/-- The identical joint action class is retained when the geometric point changes. -/
@[simp] theorem forgetDimensionLieAction_classPointMap
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) (U : Level)
    (q : classesAt s hs htor hu additivity U) :
    forgetJointAt t ht htor hu additivity (moveClass path U q) =
      forgetJointAt s hs htor hu additivity q := by
  obtain ⟨x, hx, hq⟩ := classOf_surjective D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality L p compatibility h
    s hs htor hu additivity q
  rw [← hq]
  rfl

/-- The entire point comparison commutes with forgetting to the joint action-class tower. -/
theorem forgetDimensionLieActionNatTrans_classPointTowerIso
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (moveTower path).hom ≫ forgetJointTowerAt t ht htor hu additivity =
      forgetJointTowerAt s hs htor hu additivity := by
  ext U q
  exact forgetDimensionLieAction_classPointMap D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality L p compatibility h
    htor hu additivity path U q

section Geometric
variable [ConnectedSpace S] [IsLocallyNoetherian S]

/-- Canonical comparison of the original Harris dimension-and-positive-Lie class towers. -/
def classGeometricPointTowerIso
    {Ωa Ωb : Type} [Field Ωa] [IsAlgClosed Ωa] [Field Ωb] [IsAlgClosed Ωb]
    (a : Spec (.of Ωa) ⟶ S) (b : Spec (.of Ωb) ⟶ S)
    (ha : ∀ Y : Cover S, Finite (Fiber a Y)) (hb : ∀ Y : Cover S, Finite (Fiber b Y)) :
    towerAt a ha htor hu additivity ≅ towerAt b hb htor hu additivity :=
  moveTower (Classical.choice (geometricPathExists a b ha hb))

local notation "geometricMove" => classGeometricPointTowerIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality L p
  compatibility h htor hu additivity

variable [IsAlgClosed Ω] [IsAlgClosed Ω'] [IsAlgClosed Ω'']

theorem classGeometricPointTowerIso_eq_path (path : fiberFunctor s hs ≅ fiberFunctor t ht) :
    geometricMove s t hs ht = moveTower path :=
  classPointTowerIso_path_independent D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality L p compatibility h htor hu additivity _ path

@[simp] theorem classGeometricPointTowerIso_refl :
    geometricMove s s hs hs = Iso.refl (towerAt s hs htor hu additivity) := by
  rw [classGeometricPointTowerIso_eq_path D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality L p compatibility h htor hu additivity
    (Iso.refl (fiberFunctor s hs))]
  exact classPointTowerIso_refl D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality L p compatibility h htor hu additivity

theorem classGeometricPointTowerIso_trans :
    geometricMove s r hs hr = geometricMove s t hs ht ≪≫ geometricMove t r ht hr := by
  let path := Classical.choice (geometricPathExists s t hs ht)
  let path2 := Classical.choice (geometricPathExists t r ht hr)
  rw [classGeometricPointTowerIso_eq_path D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality L p compatibility h htor hu additivity (path ≪≫ path2),
    classGeometricPointTowerIso_eq_path D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality L p compatibility h htor hu additivity path,
    classGeometricPointTowerIso_eq_path D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality L p compatibility h htor hu additivity path2]
  exact classPointTowerIso_trans D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality L p compatibility h htor hu additivity path path2

theorem classGeometricPointTowerIso_symm :
    (geometricMove s t hs ht).symm = geometricMove t s ht hs := by
  let path := Classical.choice (geometricPathExists s t hs ht)
  rw [classGeometricPointTowerIso_eq_path D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality L p compatibility h htor hu additivity path,
    classGeometricPointTowerIso_eq_path D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality L p compatibility h htor hu additivity path.symm]
  exact classPointTowerIso_symm D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality L p compatibility h htor hu additivity path

end Geometric
end Langlands.Shimura.PEL.HarrisTaylorLieWeilLevel
