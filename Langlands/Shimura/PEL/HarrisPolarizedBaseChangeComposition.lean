import Langlands.Shimura.PEL.HarrisPolarizedBaseChangeIdentity

/-! # Composition of actual Harris polarized level pullback -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
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
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  {S T R : Scheme.{0}} (b : T ⟶ S) (c : R ⟶ T)

variable [QuasiSeparatedSpace S] [QuasiSeparatedSpace T] [QuasiSeparatedSpace R]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (t : Spec (.of Ω) ⟶ R)
  (ht : ∀ Y : Cover R, Finite (Fiber t Y))
  (htc : ∀ Y : Cover T, Finite (Fiber (t ≫ c) Y))
  (hs : ∀ Y : Cover S, Finite (Fiber ((t ≫ c) ≫ b) Y))
  (hd : ∀ Y : Cover S, Finite (Fiber (t ≫ (c ≫ b)) Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T, ⊤)))
  (huR : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(R, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T k.val).X.hom]
  [hμetT : ∀ k : Index (fun _ => True), Etale (mu T k.val).X.hom]
  [hμfinR : ∀ k : Index (fun _ => True), IsFinite (mu R k.val).X.hom]
  [hμetR : ∀ k : Index (fun _ => True), Etale (mu R k.val).X.hom]
  (dualB : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality b X)
  (dualC : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T),
    PositivePullbackDualData D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality c X)
  (dualD : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality (c ≫ b) X)

local notation "DataS" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  ((t ≫ c) ≫ b) hs htor huS
local notation "indexFunctor" => hodgeLevelFunctor D C
local notation "pullB" => levelDataBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h (t ≫ c) htc hs htor huS huT dualB
local notation "pullC" => levelDataBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability c compatibility h t ht htc htor huT huR dualC
local notation "pullD" => levelDataBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability (c ≫ b) compatibility h t ht hd htor huS huR dualD
local notation "moveData" => levelDataPointEq D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor huS

/-- The canonical action isomorphism from the actual directly pulled
representative to the actual successively pulled representative. -/
def levelDataBaseChangeCompIso (U : HarrisLevel D) (x : DataS U) :
    letI := auxiliaryStarRing D C
    (pullD U (moveData (Category.assoc t c b) hs hd U x)).1.actionObj ≅
      (pullC U (pullB U x)).1.actionObj := by
  let := auxiliaryStarRing D C
  exact RationalAlgebraAction.pullbackCompIso b c x.1.actionObj

local notation "compAction" => levelDataBaseChangeCompIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b c compatibility h t ht htc hs hd htor
  huS huT huR dualB dualC dualD

variable
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (addT : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T))
  (addR : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := R))

/-- The actual direct-to-successive action comparison has geometric multiplier
one for the independently constructed duals and pulled polarizations. -/
lemma levelDataBaseChange_comp_multiple (U : HarrisLevel D) (x : DataS U) :
    letI := auxiliaryStarRing D C
    PolarizedWeilLevel.Multiple preservation composition unitCoherence associativity
      comparison symmetry stability square universality addR
      (pullD U (moveData (Category.assoc t c b) hs hd U x)).1
      (pullC U (pullB U x)).1 1
      (compAction U x) := by
  let := auxiliaryStarRing D C
  let Wb := dualB x.1
  let Wd := dualD x.1
  let Wc := dualC (pullB U x).1
  have hm := rationalDualBaseChangeHom_comp_multiple preservation stability composition
    unitCoherence associativity comparison symmetry universality dualAbelianBaseChange
    x.1.actionObj.abelianScheme x.1.hasDual x.1.geometry x.1.inversePoincare x.1.evaluation
    b c Wb.hasDual Wb.geometry Wb.inversePoincare Wb.evaluation
    Wd.hasDual Wd.geometry Wd.inversePoincare Wd.evaluation
    Wc.hasDual Wc.geometry Wc.inversePoincare Wc.evaluation
    (addR (pullD U (moveData (Category.assoc t c b) hs hd U x)).1
      (pullC U (pullB U x)).1) (homToHom0 x.1.polarization)
  rw [rationalDualBaseChangeHom_homToHom0, rationalDualBaseChangeHom_homToHom0,
    rationalDualBaseChangeHom_homToHom0] at hm
  exact hm

/-- The polarized isogeny level map of the actual direct-to-successive
comparison is the geometric Tate composition comparison. -/
lemma levelIso_pullbackComp (U : HarrisLevel D) (x : DataS U)
    (z : letI := auxiliaryStarRing D C
      (PolarizedWeilLevel.levelTower preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h A
        (D.harrisHodgePELForm C) t ht htor huR
        (pullD U (moveData (Category.assoc t c b) hs hd U x)).1).obj
        ((indexFunctor).obj U)) :
    letI := auxiliaryStarRing D C
    PolarizedWeilLevel.levelIso preservation composition unitCoherence associativity
      comparison symmetry stability square universality compatibility h A
      (D.harrisHodgePELForm C) t ht htor huR addR
      (pullD U (moveData (Category.assoc t c b) hs hd U x)).1
      (pullC U (pullB U x)).1 ((indexFunctor).obj U) 1
      (compAction U x)
      (levelDataBaseChange_comp_multiple D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability b c compatibility h t ht htc hs hd htor huS huT huR
        dualB dualC dualD addR U x) z =
    Tate.weilAdelicLevelBaseChangeComp preservation composition unitCoherence associativity
      comparison symmetry stability x.1.hasDual x.1.geometry x.1.inversePoincare
      x.1.evaluation compatibility x.1.polarization h x.1.actionObj.action A
      (D.harrisHodgePELForm C) b c universality
      (dualB x.1).hasDual (dualB x.1).geometry (dualB x.1).inversePoincare
      (dualB x.1).evaluation
      (dualD x.1).hasDual (dualD x.1).geometry (dualD x.1).inversePoincare
      (dualD x.1).evaluation
      (dualC (pullB U x).1).hasDual (dualC (pullB U x).1).geometry
      (dualC (pullB U x).1).inversePoincare (dualC (pullB U x).1).evaluation
      t ht htor huR ((indexFunctor).obj U).toSubgroup z := by
  let := auxiliaryStarRing D C
  let xd := pullD U (moveData (Category.assoc t c b) hs hd U x)
  let xc := pullC U (pullB U x)
  let := Tate.weilAdelicFrameRightAction preservation composition unitCoherence associativity
    comparison symmetry stability xd.1.hasDual xd.1.geometry xd.1.inversePoincare
    xd.1.evaluation compatibility xd.1.polarization h xd.1.actionObj.action A
    (D.harrisHodgePELForm C) t
  let := Tate.weilAdelicFrameRightAction preservation composition unitCoherence associativity
    comparison symmetry stability xc.1.hasDual xc.1.geometry xc.1.inversePoincare
    xc.1.evaluation compatibility xc.1.polarization h xc.1.actionObj.action A
    (D.harrisHodgePELForm C) t
  apply Subtype.ext
  simp only [PolarizedWeilLevel.levelIso, Tate.weilAdelicLevelIsogeny,
    Tate.weilAdelicLevelBaseChangeComp, InvariantOrbit.equiv, Equiv.coe_fn_mk,
    InvariantOrbit.map_val]
  apply RightOrbit.map_congr (G := ScalarExtensionSimilitudes A A (Global.FiniteAdeles ℚ)
    (D.harrisHodgePELForm C))
  · apply Tate.weilAdelicFrameIsogeny_right
  · intro eta
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    simp only [Tate.weilAdelicFrameIsogeny_apply, levelDataBaseChangeCompIso,
      RationalAlgebraAction.underlyingIso_pullbackCompIso]
    exact congrFun (congrArg DFunLike.coe (Tate.rationalHomMap_ofHom
      (Over.mk t) (fun _ => True) (baseChangeCompIso b c x.1.actionObj.abelianScheme).hom))
      (eta.1 v) |>.trans
        (Tate.weilAdelicFrameBaseChangeComp_apply preservation composition unitCoherence
          associativity comparison symmetry stability x.1.hasDual x.1.geometry
          x.1.inversePoincare x.1.evaluation compatibility x.1.polarization h
          x.1.actionObj.action A (D.harrisHodgePELForm C) b c universality
          (dualB x.1).hasDual (dualB x.1).geometry (dualB x.1).inversePoincare
          (dualB x.1).evaluation
          (dualD x.1).hasDual (dualD x.1).geometry (dualD x.1).inversePoincare
          (dualD x.1).evaluation
          (dualC (pullB U x).1).hasDual (dualC (pullB U x).1).geometry
          (dualC (pullB U x).1).inversePoincare (dualC (pullB U x).1).evaluation
          t eta v).symm

local notation "relAt" => PolarizedWeilLevel.isogenySetoid preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h A (D.harrisHodgePELForm C)

/-- The actual direct and successive pulled level representatives are related
by the canonical equivariant comparison, with geometric multiplier one. -/
theorem levelDataBaseChange_comp_related (U : HarrisLevel D) (x : DataS U) :
    letI := auxiliaryStarRing D C
    (relAt t ht htor huR addR ((indexFunctor).obj U)).r
      (pullD U (moveData (Category.assoc t c b) hs hd U x))
      (pullC U (pullB U x)) := by
  let := auxiliaryStarRing D C
  refine ⟨1, compAction U x,
    levelDataBaseChange_comp_multiple D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability b c compatibility h t ht htc hs hd htor huS huT huR
      dualB dualC dualD addR U x, ?_⟩
  rw [levelIso_pullbackComp D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b c compatibility h t ht htc hs hd htor huS huT huR
    dualB dualC dualD addR U x]
  exact Tate.weilAdelicLevelBaseChange_comp preservation composition unitCoherence
    associativity comparison symmetry stability x.1.hasDual x.1.geometry
    x.1.inversePoincare x.1.evaluation compatibility x.1.polarization h
    x.1.actionObj.action A (D.harrisHodgePELForm C) b c universality
    (dualB x.1).hasDual (dualB x.1).geometry (dualB x.1).inversePoincare
    (dualB x.1).evaluation
    (dualD x.1).hasDual (dualD x.1).geometry (dualD x.1).inversePoincare
    (dualD x.1).evaluation
    (dualC (pullB U x).1).hasDual (dualC (pullB U x).1).geometry
    (dualC (pullB U x).1).inversePoincare (dualC (pullB U x).1).evaluation
    t ht htor huR huS huT htc hs hd ((indexFunctor).obj U).toSubgroup x.2

local notation "pullClassB" => ambientClassBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h (t ≫ c) htc hs htor huS huT dualB addS addT
local notation "pullClassC" => ambientClassBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability c compatibility h t ht htc htor huT huR dualC addT addR
local notation "pullClassD" => ambientClassBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability (c ≫ b) compatibility h t ht hd htor huS huR dualD addS addR
local notation "moveClass" => ambientClassPointEq D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor huS addS

/-- Successive actual pullback of ambient classes equals direct pullback after
the canonical associativity transport of the source point. -/
theorem ambientClassBaseChange_comp (U : HarrisLevel D) :
    letI := auxiliaryStarRing D C
    pullClassC U ∘ pullClassB U =
      pullClassD U ∘ moveClass (Category.assoc t c b) hs hd U := by
  let := auxiliaryStarRing D C
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  simp only [Function.comp_apply, ambientClassBaseChange_mk, ambientClassPointEq_mk]
  exact (Quotient.sound (levelDataBaseChange_comp_related D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability b c compatibility h t ht htc hs hd htor
    huS huT huR dualB dualC dualD addR U x)).symm

local notation "pullTowerB" => ambientClassTowerBaseChange D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h (t ≫ c) htc hs htor
  huS huT dualB addS addT
local notation "pullTowerC" => ambientClassTowerBaseChange D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability c compatibility h t ht htc htor
  huT huR dualC addT addR
local notation "pullTowerD" => ambientClassTowerBaseChange D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability (c ≫ b) compatibility h t ht hd htor
  huS huR dualD addS addR
local notation "moveTower" => ambientClassTowerPointEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor huS addS

/-- Composition holds on the original Harris class towers, including every
level and Hecke transporter arrow. -/
theorem ambientClassTowerBaseChange_comp :
    letI := auxiliaryStarRing D C
    pullTowerB ≫ pullTowerC =
      moveTower (Category.assoc t c b) hs hd ≫ pullTowerD := by
  let := auxiliaryStarRing D C
  ext U q
  exact congrFun (ambientClassBaseChange_comp D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b c compatibility h t ht htc hs hd htor huS huT huR
    dualB dualC dualD addS addT addR U) q

/-- The composition law for the choice-independent tower maps constructed
from existence of actual dual-evaluation inputs. -/
theorem ambientClassTowerBaseChangeOfExists_comp
    (existsB : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := S),
      Nonempty (PositivePullbackDualData D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality b X))
    (existsC : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := T),
      Nonempty (PositivePullbackDualData D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality c X))
    (existsD : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := S),
      Nonempty (PositivePullbackDualData D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality (c ≫ b) X)) :
    letI := auxiliaryStarRing D C
    ambientClassTowerBaseChangeOfExists D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability b compatibility h (t ≫ c) htc hs htor huS huT
      addS addT existsB ≫
    ambientClassTowerBaseChangeOfExists D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability c compatibility h t ht htc htor huT huR
      addT addR existsC =
    moveTower (Category.assoc t c b) hs hd ≫
    ambientClassTowerBaseChangeOfExists D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability (c ≫ b) compatibility h t ht hd htor huS huR
      addS addR existsD := by
  let := auxiliaryStarRing D C
  exact ambientClassTowerBaseChange_comp D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b c compatibility h t ht htc hs hd htor huS huT huR
    (fun X => Classical.choice (existsB X))
    (fun X => Classical.choice (existsC X))
    (fun X => Classical.choice (existsD X)) addS addT addR

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
