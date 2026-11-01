import Langlands.Shimura.PEL.PolarizedWeilLevelClasses
import Langlands.AbelianScheme.Tate.WeilCompactOpenLevelTransport

/-! # Point independence of actual polarized Weil level classes -/

universe u v w

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.PolarizedWeilLevel

open Langlands.AbelianScheme Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (square : MumfordBundlePicardZeroStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})
  {S : Scheme.{u}} {D : Type v} [Ring D] [Algebra ℚ D] [StarRing D]
  [QuasiSeparatedSpace S]
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  {hr : ∀ Y : Cover S, Finite (Fiber r Y)}

local notation "Level" => FiniteAdelicScalarExtensionLevel D V ψ
local notation "dataAt" => LevelData preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ

/-- Change only the point presentation of the actual compatible level orbit. -/
def pointMapData (p : fiberFunctor s hs ≅ fiberFunctor t ht) (K : Level)
    (x : dataAt s hs htor hu K) : dataAt t ht htor hu K :=
  ⟨x.1, (weilAdelicCompactOpenLevelTransport preservation composition unitCoherence
    associativity comparison symmetry stability compatibility x.1.hasDual x.1.geometry
    x.1.inversePoincare x.1.evaluation x.1.polarization h x.1.actionObj.action
    V ψ htor hu p).hom.app K x.2⟩

local notation "move" => pointMapData preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ htor hu

@[simp] theorem pointMapData_fst (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (K : Level) (x : dataAt s hs htor hu K) : (move p K x).1 = x.1 := rfl

/-- Fixed orbits erase the auxiliary path while retaining the identical polarized object. -/
theorem pointMapData_path_independent (p q : fiberFunctor s hs ≅ fiberFunctor t ht)
    (K : Level) (x : dataAt s hs htor hu K) : move p K x = move q K x := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  exact congrArg (fun e => e.hom.app K x.2)
    (weilAdelicCompactOpenLevelTransport_path_independent preservation composition
      unitCoherence associativity comparison symmetry stability compatibility x.1.hasDual
      x.1.geometry x.1.inversePoincare x.1.evaluation x.1.polarization h
      x.1.actionObj.action V ψ htor hu p q)

@[simp] theorem pointMapData_refl (K : Level) (x : dataAt s hs htor hu K) :
    move (Iso.refl (fiberFunctor s hs)) K x = x := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  exact congrArg (fun e => e.hom.app K x.2)
    (weilAdelicCompactOpenLevelTransport_refl preservation composition unitCoherence
      associativity comparison symmetry stability compatibility x.1.hasDual x.1.geometry
      x.1.inversePoincare x.1.evaluation x.1.polarization h x.1.actionObj.action V ψ htor hu)

/-- The representative transport has the actual path-composition law. -/
theorem pointMapData_trans (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (q : fiberFunctor t ht ≅ fiberFunctor r hr) (K : Level)
    (x : dataAt s hs htor hu K) : move (p ≪≫ q) K x = move q K (move p K x) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  exact congrArg (fun e => e.hom.app K x.2)
    (weilAdelicCompactOpenLevelTransport_trans preservation composition unitCoherence
      associativity comparison symmetry stability compatibility x.1.hasDual x.1.geometry
      x.1.inversePoincare x.1.evaluation x.1.polarization h x.1.actionObj.action V ψ htor hu p q)

variable (additivity : PairAdditivity preservation composition unitCoherence associativity
  comparison symmetry stability square universality (S := S) (D := D))

local notation "relAt" => isogenySetoid preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ
local notation "classesAt" => IsoClass preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ

/-- The same rational isomorphism and geometric multiplier relate transported representatives. -/
theorem pointMapData_related (p : fiberFunctor s hs ≅ fiberFunctor t ht) (K : Level)
    {x y : dataAt s hs htor hu K} (hxy : (relAt s hs htor hu additivity K).r x y) :
    (relAt t ht htor hu additivity K).r (move p K x) (move p K y) := by
  obtain ⟨q, e, he, hxy⟩ := hxy
  refine ⟨q, e, he, ?_⟩
  have sq := weilAdelicLevelIsogeny_transport preservation composition unitCoherence
    associativity comparison symmetry stability x.1.hasDual y.1.hasDual x.1.geometry
    y.1.geometry x.1.inversePoincare x.1.evaluation y.1.inversePoincare y.1.evaluation
    (additivity x.1 y.1) x.1.polarization y.1.polarization compatibility
    rationalWeilFunctoriality rationalWeilGeometricTransport h x.1.actionObj.action
    y.1.actionObj.action V ψ s hs htor hu K.toSubgroup q
    (RationalAlgebraAction.underlyingIso e) (RationalAlgebraAction.intertwines e.hom) he p x.2
  exact sq.symm.trans (congrArg (fun z =>
    (weilAdelicCompactOpenLevelTransport preservation composition unitCoherence
      associativity comparison symmetry stability compatibility y.1.hasDual y.1.geometry
      y.1.inversePoincare y.1.evaluation y.1.polarization h y.1.actionObj.action
      V ψ htor hu p).hom.app K z) hxy)

/-- Actual path transport descended through the polarized rational-isogeny relation. -/
def classPointMap (p : fiberFunctor s hs ≅ fiberFunctor t ht) (K : Level) :
    classesAt s hs htor hu additivity K → classesAt t ht htor hu additivity K :=
  Quotient.map (move p K) (fun _ _ hxy => pointMapData_related preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h V ψ htor hu additivity p K hxy)

local notation "moveClass" => classPointMap preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ htor hu additivity

@[simp] theorem classPointMap_mk (p : fiberFunctor s hs ≅ fiberFunctor t ht) (K : Level)
    (x : dataAt s hs htor hu K) :
    moveClass p K (Quotient.mk _ x) = Quotient.mk _ (move p K x) := rfl

/-- Path independence already holds on actual representatives and hence on classes. -/
theorem classPointMap_path_independent (p q : fiberFunctor s hs ≅ fiberFunctor t ht)
    (K : Level) : moveClass p K = moveClass q K := by
  funext x
  refine Quotient.inductionOn x ?_
  intro x
  exact congrArg (Quotient.mk _) (pointMapData_path_independent preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h V ψ htor hu p q K x)

@[simp] theorem classPointMap_refl (K : Level) (x : classesAt s hs htor hu additivity K) :
    moveClass (Iso.refl (fiberFunctor s hs)) K x = x := by
  refine Quotient.inductionOn x ?_
  intro x
  exact congrArg (Quotient.mk _) (pointMapData_refl preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h V ψ htor hu K x)

theorem classPointMap_trans (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (q : fiberFunctor t ht ≅ fiberFunctor r hr) (K : Level)
    (x : classesAt s hs htor hu additivity K) :
    moveClass (p ≪≫ q) K x = moveClass q K (moveClass p K x) := by
  refine Quotient.inductionOn x ?_
  intro x
  exact congrArg (Quotient.mk _) (pointMapData_trans preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h V ψ htor hu p q K x)

/-- Reverse-path transport is an actual two-sided inverse on classes. -/
def classPointEquiv (p : fiberFunctor s hs ≅ fiberFunctor t ht) (K : Level) :
    classesAt s hs htor hu additivity K ≃ classesAt t ht htor hu additivity K where
  toFun := moveClass p K
  invFun := moveClass p.symm K
  left_inv x := by
    rw [← classPointMap_trans, Iso.self_symm_id, classPointMap_refl]
  right_inv x := by
    rw [← classPointMap_trans, Iso.symm_self_id, classPointMap_refl]

local notation "mapDataAt" => mapData preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ

/-- Change of point commutes with every compact-open transporter on actual representatives. -/
theorem pointMapData_mapData (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    {K L : Level} (f : K ⟶ L) (x : dataAt s hs htor hu K) :
    move p L (mapDataAt s hs htor hu f x) = mapDataAt t ht htor hu f (move p K x) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  exact NatTrans.naturality_apply
    (weilAdelicCompactOpenLevelTransport preservation composition unitCoherence
      associativity comparison symmetry stability compatibility x.1.hasDual x.1.geometry
      x.1.inversePoincare x.1.evaluation x.1.polarization h x.1.actionObj.action V ψ htor hu p).hom f x.2

local notation "classTowerAt" => isoClassTower preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h V ψ

/-- Point transport is an isomorphism of the actual polarized-isogeny class towers. -/
def classPointTowerIso (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    classTowerAt s hs htor hu additivity ≅ classTowerAt t ht htor hu additivity :=
  NatIso.ofComponents (fun K => (classPointEquiv preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h
    V ψ htor hu additivity p K).toIso) (by
      intro K L f
      ext x
      refine Quotient.inductionOn x ?_
      intro x
      exact congrArg (Quotient.mk _) (pointMapData_mapData preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        compatibility h V ψ htor hu p f x))

local notation "moveTower" => classPointTowerIso preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h V ψ htor hu additivity

@[simp] theorem classPointTowerIso_hom_app (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (K : Level) (x : classesAt s hs htor hu additivity K) :
    (moveTower p).hom.app K x = moveClass p K x := rfl

@[simp] theorem classPointTowerIso_inv_app (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (K : Level) (x : classesAt t ht htor hu additivity K) :
    (moveTower p).inv.app K x = moveClass p.symm K x := rfl

theorem classPointTowerIso_symm (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (moveTower p).symm = moveTower p.symm := by
  apply Iso.ext
  ext K x
  rfl

theorem classPointTowerIso_path_independent (p q : fiberFunctor s hs ≅ fiberFunctor t ht) :
    moveTower p = moveTower q := by
  apply Iso.ext
  ext K x
  exact congrFun (classPointMap_path_independent preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h
    V ψ htor hu additivity p q K) x

@[simp] theorem classPointTowerIso_refl :
    moveTower (Iso.refl (fiberFunctor s hs)) = Iso.refl (classTowerAt s hs htor hu additivity) := by
  apply Iso.ext
  ext K x
  exact classPointMap_refl preservation composition unitCoherence associativity comparison
    symmetry stability square universality compatibility h V ψ htor hu additivity K x

theorem classPointTowerIso_trans (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (q : fiberFunctor t ht ≅ fiberFunctor r hr) :
    moveTower (p ≪≫ q) = moveTower p ≪≫ moveTower q := by
  apply Iso.ext
  ext K x
  exact classPointMap_trans preservation composition unitCoherence associativity comparison
    symmetry stability square universality compatibility h V ψ htor hu additivity p q K x

/-- Changing the point leaves the underlying actual rational action class identical. -/
@[simp] theorem forgetAction_classPointMap (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (K : Level) (x : classesAt s hs htor hu additivity K) :
    forgetAction preservation composition unitCoherence associativity comparison symmetry
      stability square universality compatibility h V ψ t ht htor hu additivity
      (moveClass p K x) =
    forgetAction preservation composition unitCoherence associativity comparison symmetry
      stability square universality compatibility h V ψ s hs htor hu additivity x := by
  refine Quotient.inductionOn x ?_
  intro x
  rfl

/-- The natural forgetful square for the entire class tower. -/
theorem forgetActionNatTrans_classPointTowerIso
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (moveTower p).hom ≫ forgetActionNatTrans preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h V ψ
      t ht htor hu additivity =
    forgetActionNatTrans preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h V ψ s hs htor hu additivity := by
  ext K x
  exact congrArg ULift.up (forgetAction_classPointMap preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h V ψ
    htor hu additivity p K x)

section Geometric
variable [ConnectedSpace S] [IsLocallyNoetherian S]

/-- Canonical point comparison of the actual polarized class tower, using proved path existence. -/
def classGeometricPointTowerIso
    {Ωa Ωb : Type u} [Field Ωa] [IsAlgClosed Ωa] [Field Ωb] [IsAlgClosed Ωb]
    (a : Spec (.of Ωa) ⟶ S) (b : Spec (.of Ωb) ⟶ S)
    (ha : ∀ Y : Cover S, Finite (Fiber a Y)) (hb : ∀ Y : Cover S, Finite (Fiber b Y)) :
    classTowerAt a ha htor hu additivity ≅ classTowerAt b hb htor hu additivity :=
  moveTower (Classical.choice (geometricPathExists a b ha hb))

local notation "geometricMove" => classGeometricPointTowerIso preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h V ψ htor hu additivity

variable [IsAlgClosed Ω] [IsAlgClosed Ω'] [IsAlgClosed Ω'']

theorem classGeometricPointTowerIso_eq_path (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    geometricMove s t hs ht = moveTower p :=
  classPointTowerIso_path_independent preservation composition unitCoherence associativity
    comparison symmetry stability square universality compatibility h V ψ htor hu additivity _ p

@[simp] theorem classGeometricPointTowerIso_refl :
    geometricMove s s hs hs = Iso.refl (classTowerAt s hs htor hu additivity) := by
  rw [classGeometricPointTowerIso_eq_path preservation composition unitCoherence associativity
    comparison symmetry stability square universality compatibility h V ψ htor hu additivity
    (Iso.refl (fiberFunctor s hs))]
  exact classPointTowerIso_refl preservation composition unitCoherence associativity comparison
    symmetry stability square universality compatibility h V ψ htor hu additivity

theorem classGeometricPointTowerIso_trans :
    geometricMove s r hs hr =
      geometricMove s t hs ht ≪≫ geometricMove t r ht hr := by
  let p := Classical.choice (geometricPathExists s t hs ht)
  let q := Classical.choice (geometricPathExists t r ht hr)
  rw [classGeometricPointTowerIso_eq_path preservation composition unitCoherence associativity
      comparison symmetry stability square universality compatibility h V ψ htor hu additivity (p ≪≫ q),
    classGeometricPointTowerIso_eq_path preservation composition unitCoherence associativity
      comparison symmetry stability square universality compatibility h V ψ htor hu additivity p,
    classGeometricPointTowerIso_eq_path preservation composition unitCoherence associativity
      comparison symmetry stability square universality compatibility h V ψ htor hu additivity q]
  exact classPointTowerIso_trans preservation composition unitCoherence associativity comparison
    symmetry stability square universality compatibility h V ψ htor hu additivity p q

theorem classGeometricPointTowerIso_symm :
    (geometricMove s t hs ht).symm = geometricMove t s ht hs := by
  let p := Classical.choice (geometricPathExists s t hs ht)
  rw [classGeometricPointTowerIso_eq_path preservation composition unitCoherence associativity
      comparison symmetry stability square universality compatibility h V ψ htor hu additivity p,
    classGeometricPointTowerIso_eq_path preservation composition unitCoherence associativity
      comparison symmetry stability square universality compatibility h V ψ htor hu additivity p.symm]
  exact classPointTowerIso_symm preservation composition unitCoherence associativity comparison
    symmetry stability square universality compatibility h V ψ htor hu additivity p

end Geometric
end Langlands.Shimura.PEL.PolarizedWeilLevel
