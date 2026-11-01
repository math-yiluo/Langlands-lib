import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedClasses
import Langlands.Shimura.PEL.HarrisTaylorLiePointTransport

/-! # Point independence of normalized CM polarized Harris classes -/

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

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "reflexStructure" => D.harrisTaylorReflexStructure C p
local notation "Level" => HarrisLevel D
local notation "indexFunctor" => hodgeLevelFunctor D C
local notation "dataAt" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
local notation "Good" => PositiveObjectCondition D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality reflexStructure
local notation "Num" => HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality L p
local notation "detClassesAt" => HarrisIsoClass D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality reflexStructure
  compatibility h
local notation "detMkAt" => harrisClassOf D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality reflexStructure
  compatibility h
local notation "conditionAt" => HarrisNumericalWeilLevel.ClassCondition D C hΦ preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  reflexStructure compatibility h
local notation "classesAt" => HarrisNumericalWeilLevel.IsoClass D C hΦ preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  reflexStructure compatibility h
local notation "mkAt" => HarrisNumericalWeilLevel.classOf D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality reflexStructure
  compatibility h
local notation "towerAt" => HarrisNumericalWeilLevel.isoClassTower D C hΦ preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  reflexStructure compatibility h
local notation "moveRep" => HarrisTaylorLieWeilLevel.pointMapRepresentative D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor hu
local notation "moveRaw" => HarrisTaylorLieWeilLevel.ambientPointTowerIso D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor hu additivity
local notation "forgetCMAt" => forgetCMAction D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h
local notation "forgetCMTowerAt" => forgetCMActionNatTrans D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p compatibility h

/-- Restrict the existing actual ambient point map to normalized determinant classes. -/
def determinantClassPointMap (path : fiberFunctor s hs ≅ fiberFunctor t ht) (U : Level)
    (q : detClassesAt s hs htor hu additivity U) :
    detClassesAt t ht htor hu additivity U := by
  letI := auxiliaryStarRing D C
  refine ⟨(moveRaw path).hom.app U q.val, ?_⟩
  change D.HarrisRationalLieDeterminantClassCondition C hΦ reflexStructure
    (PolarizedWeilLevel.forgetAction preservation composition unitCoherence associativity
      comparison symmetry stability square universality compatibility h A
      (D.harrisHodgePELForm C) t ht htor hu additivity
      (PolarizedWeilLevel.classPointMap preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h A
        (D.harrisHodgePELForm C) htor hu additivity path ((indexFunctor).obj U) q.val))
  rw [PolarizedWeilLevel.forgetAction_classPointMap]
  exact q.property

local notation "moveDet" => determinantClassPointMap D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h htor hu additivity

omit [IsCMField F] in
@[simp] theorem determinantClassPointMap_val (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : Level) (q : detClassesAt s hs htor hu additivity U) :
    (moveDet path U q).val = (moveRaw path).hom.app U q.val := rfl

omit [IsCMField F] in
@[simp] theorem determinantClassPointMap_classOf (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : Level) (x : dataAt s hs htor hu U) (hx : Good x.1) :
    moveDet path U (detMkAt s hs htor hu additivity x hx) =
      detMkAt t ht htor hu additivity (moveRep path U x) hx := rfl

/-- The same normalized determinant and numerical witness survives the point change. -/
theorem classCondition_pointMap (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : Level) (q : detClassesAt s hs htor hu additivity U)
    (hq : conditionAt s hs htor hu additivity L p q) :
    conditionAt t ht htor hu additivity L p (moveDet path U q) := by
  obtain ⟨x, hx, hq, hn⟩ := hq
  refine ⟨moveRep path U x, hx, ?_, hn⟩
  rw [← hq]
  rfl

/-- Change only the orbit's point presentation in the existing normalized CM class image. -/
def classPointMap (path : fiberFunctor s hs ≅ fiberFunctor t ht) (U : Level)
    (q : classesAt s hs htor hu additivity L p U) :
    classesAt t ht htor hu additivity L p U :=
  ⟨moveDet path U q.val, classCondition_pointMap D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality p
    compatibility h htor hu additivity path U q.val q.property⟩

local notation "moveClass" => classPointMap D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h
  htor hu additivity

@[simp] theorem classPointMap_val (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : Level) (q : classesAt s hs htor hu additivity L p U) :
    (moveClass path U q).val = moveDet path U q.val := rfl

@[simp] theorem classPointMap_classOf (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : Level) (x : dataAt s hs htor hu U) (hx : Good x.1) (hn : Num x.1) :
    moveClass path U (mkAt s hs htor hu additivity L p x hx hn) =
      mkAt t ht htor hu additivity L p (moveRep path U x) hx hn := rfl

/-- Reversing the actual fibre-functor path inverts the restricted class map. -/
def classPointEquiv (path : fiberFunctor s hs ≅ fiberFunctor t ht) (U : Level) :
    classesAt s hs htor hu additivity L p U ≃ classesAt t ht htor hu additivity L p U where
  toFun := moveClass path U
  invFun := moveClass path.symm U
  left_inv q := by
    let := auxiliaryStarRing D C
    apply Subtype.ext
    apply Subtype.ext
    exact (PolarizedWeilLevel.classPointEquiv preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h A
      (D.harrisHodgePELForm C) htor hu additivity path ((indexFunctor).obj U)).left_inv q.val.val
  right_inv q := by
    let := auxiliaryStarRing D C
    apply Subtype.ext
    apply Subtype.ext
    exact (PolarizedWeilLevel.classPointEquiv preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h A
      (D.harrisHodgePELForm C) htor hu additivity path ((indexFunctor).obj U)).right_inv q.val.val

/-- Actual point comparison is natural for every original Harris level transporter. -/
def classPointTowerIso (path : fiberFunctor s hs ≅ fiberFunctor t ht) :
    towerAt s hs htor hu additivity L p ≅ towerAt t ht htor hu additivity L p :=
  NatIso.ofComponents (fun U => (classPointEquiv D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality p compatibility h
    htor hu additivity path U).toIso) (by
      intro U V f
      ext q
      apply Subtype.ext
      apply Subtype.ext
      exact (moveRaw path).hom.naturality_apply f q.val.val)

local notation "moveTower" => classPointTowerIso D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h
  htor hu additivity

@[simp] theorem classPointTowerIso_hom_app (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : Level) (q : classesAt s hs htor hu additivity L p U) :
    (moveTower path).hom.app U q = moveClass path U q := rfl

@[simp] theorem classPointTowerIso_inv_app (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : Level) (q : classesAt t ht htor hu additivity L p U) :
    (moveTower path).inv.app U q = moveClass path.symm U q := rfl

theorem classPointTowerIso_path_independent (path path2 : fiberFunctor s hs ≅ fiberFunctor t ht) :
    moveTower path = moveTower path2 := by
  let := auxiliaryStarRing D C
  apply Iso.ext
  ext U q
  apply Subtype.ext
  apply Subtype.ext
  exact congrFun (PolarizedWeilLevel.classPointMap_path_independent preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h A (D.harrisHodgePELForm C) htor hu additivity path path2
    ((indexFunctor).obj U)) q.val.val

@[simp] theorem classPointTowerIso_refl :
    moveTower (Iso.refl (fiberFunctor s hs)) =
      Iso.refl (towerAt s hs htor hu additivity L p) := by
  let := auxiliaryStarRing D C
  apply Iso.ext
  ext U q
  apply Subtype.ext
  apply Subtype.ext
  exact PolarizedWeilLevel.classPointMap_refl preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h A
    (D.harrisHodgePELForm C) htor hu additivity ((indexFunctor).obj U) q.val.val

theorem classPointTowerIso_trans (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (path2 : fiberFunctor t ht ≅ fiberFunctor r hr) :
    moveTower (path ≪≫ path2) = moveTower path ≪≫ moveTower path2 := by
  let := auxiliaryStarRing D C
  apply Iso.ext
  ext U q
  apply Subtype.ext
  apply Subtype.ext
  exact PolarizedWeilLevel.classPointMap_trans preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h A
    (D.harrisHodgePELForm C) htor hu additivity path path2 ((indexFunctor).obj U) q.val.val

theorem classPointTowerIso_symm (path : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (moveTower path).symm = moveTower path.symm := by
  apply Iso.ext
  ext U q
  rfl

/-- Changing the point retains the identical joint normalized CM action class. -/
@[simp] theorem forgetCMAction_classPointMap (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : Level) (q : classesAt s hs htor hu additivity L p U) :
    forgetCMAt t ht htor hu additivity (moveClass path U q) =
      forgetCMAt s hs htor hu additivity q := by
  obtain ⟨x, hx, hn, hq⟩ := HarrisNumericalWeilLevel.classOf_surjective D C hΦ
    preservation composition unitCoherence associativity comparison symmetry stability
    square universality reflexStructure compatibility h s hs htor hu additivity L p q
  rw [← hq]
  rfl

/-- Natural forgetting of polarization and level commutes with the entire point comparison. -/
theorem forgetCMActionNatTrans_classPointTowerIso
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (moveTower path).hom ≫ forgetCMTowerAt t ht htor hu additivity =
      forgetCMTowerAt s hs htor hu additivity := by
  ext U q
  exact forgetCMAction_classPointMap D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality p compatibility h
    htor hu additivity path U q

section Geometric
variable [ConnectedSpace S] [IsLocallyNoetherian S]

/-- Canonical comparison of the normalized CM determinant-and-numerical class towers. -/
def classGeometricPointTowerIso
    {Ωa Ωb : Type} [Field Ωa] [IsAlgClosed Ωa] [Field Ωb] [IsAlgClosed Ωb]
    (a : Spec (.of Ωa) ⟶ S) (b : Spec (.of Ωb) ⟶ S)
    (ha : ∀ Y : Cover S, Finite (Fiber a Y)) (hb : ∀ Y : Cover S, Finite (Fiber b Y)) :
    towerAt a ha htor hu additivity L p ≅ towerAt b hb htor hu additivity L p :=
  moveTower (Classical.choice (geometricPathExists a b ha hb))

local notation "geometricMove" => classGeometricPointTowerIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h htor hu additivity

variable [IsAlgClosed Ω] [IsAlgClosed Ω'] [IsAlgClosed Ω'']

theorem classGeometricPointTowerIso_eq_path (path : fiberFunctor s hs ≅ fiberFunctor t ht) :
    geometricMove s t hs ht = moveTower path :=
  classPointTowerIso_path_independent D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality p compatibility h htor hu additivity _ path

@[simp] theorem classGeometricPointTowerIso_refl :
    geometricMove s s hs hs = Iso.refl (towerAt s hs htor hu additivity L p) := by
  rw [classGeometricPointTowerIso_eq_path D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality p compatibility h htor hu additivity
    (Iso.refl (fiberFunctor s hs))]
  exact classPointTowerIso_refl D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality p compatibility h htor hu additivity

theorem classGeometricPointTowerIso_trans :
    geometricMove s r hs hr = geometricMove s t hs ht ≪≫ geometricMove t r ht hr := by
  let path := Classical.choice (geometricPathExists s t hs ht)
  let path2 := Classical.choice (geometricPathExists t r ht hr)
  rw [classGeometricPointTowerIso_eq_path D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p compatibility h htor hu additivity (path ≪≫ path2),
    classGeometricPointTowerIso_eq_path D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p compatibility h htor hu additivity path,
    classGeometricPointTowerIso_eq_path D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p compatibility h htor hu additivity path2]
  exact classPointTowerIso_trans D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality p compatibility h htor hu additivity path path2

theorem classGeometricPointTowerIso_symm :
    (geometricMove s t hs ht).symm = geometricMove t s ht hs := by
  let path := Classical.choice (geometricPathExists s t hs ht)
  rw [classGeometricPointTowerIso_eq_path D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p compatibility h htor hu additivity path,
    classGeometricPointTowerIso_eq_path D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p compatibility h htor hu additivity path.symm]
  exact classPointTowerIso_symm D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality p compatibility h htor hu additivity path

/-- Canonical geometric-point comparison retains the joint normalized CM action class. -/
theorem forgetCMActionNatTrans_classGeometricPointTowerIso :
    (geometricMove s t hs ht).hom ≫ forgetCMTowerAt t ht htor hu additivity =
      forgetCMTowerAt s hs htor hu additivity :=
  forgetCMActionNatTrans_classPointTowerIso D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality p compatibility h
    htor hu additivity _

end Geometric
end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
