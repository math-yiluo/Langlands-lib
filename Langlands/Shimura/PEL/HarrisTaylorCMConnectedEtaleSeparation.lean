import Langlands.Shimura.PEL.HarrisTaylorCMSquareCompatibility
import Langlands.Shimura.PEL.HarrisTaylorCMUniversalClass
import Langlands.Shimura.PEL.HarrisTaylorCMConnectedEtaleSheafStatement
import Langlands.Shimura.PEL.HarrisTaylorCMBaseAdmissibility
import Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelRigidityProof
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeExistenceProof
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeGeometryProof
import Langlands.AbelianScheme.ConnectedEtaleRationalHomDescentStatement

/-! # Separatedness of the normalized CM classes for étale covers of connected tests -/

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
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
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
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})


local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "Bases" => AdmissibleCMBaseCategory D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "tower" => unpointedClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor
local notation "pull" => unpointedClassTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "connectedClasses" => unpointedClassTowerPresheaf D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "duals" => unpointedPullbackDualData D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality

/-- Uniqueness of amalgamation for the unpointed normalized CM class presheaf
at every small level and every jointly surjective étale family of connected
admissible tests. -/
def CMConnectedEtaleSeparatedStatement : Prop :=
  ∀ (U : SmallCMLevel D) (S : Bases) (K : Type) (W : K → Bases) (g : ∀ k, W k ⟶ S),
    (∀ k, Etale (g k).hom.left) →
    (∀ x : S.obj.left, ∃ (k : K) (y : (W k).obj.left), (g k).hom.left.base y = x) →
    Presieve.IsSeparatedFor ((connectedClasses).flip.obj U.obj) (Presieve.ofArrows W g)

set_option quotPrecheck false in
local notation "CMData[" S ", " a ", " U "]" =>
  HarrisLevelData D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality compatibility h (a).hom (a).finiteFibers
    htor (S).property.torsionUnits U
local notation "fiberAt[" a "]" =>
  fiberFunctor (HarrisGeometricPoint.hom a) (HarrisGeometricPoint.finiteFibers a)
set_option quotPrecheck false in
local notation "Good[" S "]" => PositiveObjectCondition D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  (D.harrisTaylorReflexStructure C (S).obj.hom)
set_option quotPrecheck false in
local notation "Numerical[" S "]" => HarrisNumericalWeilLevel.NumericalObjectCondition D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality L (S).obj.hom
set_option quotPrecheck false in
local notation "classOfAt[" S ", " a "]" => HarrisNumericalWeilLevel.classOf D C hΦ
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality (D.harrisTaylorReflexStructure C (S).obj.hom) compatibility h
  (a).hom (a).finiteFibers htor (S).property.torsionUnits (S).property.pairAdditivity L (S).obj.hom

private def pathBetween {S : Scheme.{0}} [ConnectedSpace S] [IsLocallyNoetherian S]
    (a b : HarrisGeometricPoint S) : fiberAt[a] ≅ fiberAt[b] :=
  Classical.choice (geometricPathExists a.hom b.hom a.finiteFibers b.finiteFibers)

/-- Use the same polarized object at each point, transporting its invariant level orbit. -/
private def representativeAt {S : Bases} (s a : HarrisGeometricPoint S.obj.left)
    {U : HarrisLevel D} (x : CMData[S, s, U]) : CMData[S, a, U] :=
  HarrisTaylorLieWeilLevel.pointMapRepresentative D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h htor
    S.property.torsionUnits (pathBetween s a) U x

local notation "rep" => representativeAt D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor

set_option maxHeartbeats 1600000 in
private theorem classOf_representativeAt {S : Bases} {U : HarrisLevel D}
    (s a : HarrisGeometricPoint S.obj.left) (v : (tower S).obj U)
    (x : CMData[S, s, U]) (hx : Good[S] x.1) (hn : Numerical[S] x.1)
    (hv : classOfAt[S, s] x hx hn = v.val s) :
    v.val a = classOfAt[S, a] (rep s a x) hx hn := by
  have hab := v.property s a
  change (classGeometricPointTowerIso D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality S.obj.hom
    compatibility h htor S.property.torsionUnits S.property.pairAdditivity
    s.hom a.hom s.finiteFibers a.finiteFibers).hom.app U (v.val s) = v.val a at hab
  rw [← hv, classGeometricPointTowerIso_eq_path D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality S.obj.hom
    compatibility h htor S.property.torsionUnits S.property.pairAdditivity
    (pathBetween s a)] at hab
  exact hab.symm

set_option maxHeartbeats 3200000 in
/-- Equal pullbacks of two unpointed classes along a test morphism give, at every
geometric point of the source, a witness of the polarized isogeny relation between
the pulled-back representatives of the two classes at the image point. -/
theorem witnessAt_of_pullback_eq {U : HarrisLevel D} {S W : Bases} (g : W ⟶ S)
    (v v' : (tower S).obj U) (hvv : (pull g).app U v = (pull g).app U v')
    (a : HarrisGeometricPoint W.obj.left)
    (x y : HarrisLevelData D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h (a.comp g.hom.left).hom
      (a.comp g.hom.left).finiteFibers htor S.property.torsionUnits U)
    (hx : PositiveObjectCondition D C hΦ preservation composition unitCoherence associativity
      comparison symmetry stability square universality
      (D.harrisTaylorReflexStructure C S.obj.hom) x.1)
    (hn : HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality L
      S.obj.hom x.1)
    (hy : PositiveObjectCondition D C hΦ preservation composition unitCoherence associativity
      comparison symmetry stability square universality
      (D.harrisTaylorReflexStructure C S.obj.hom) y.1)
    (hny : HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality L
      S.obj.hom y.1)
    (hvx : v.val (a.comp g.hom.left) = HarrisNumericalWeilLevel.classOf D C hΦ preservation
      composition unitCoherence associativity comparison symmetry stability square universality
      (D.harrisTaylorReflexStructure C S.obj.hom) compatibility h (a.comp g.hom.left).hom
      (a.comp g.hom.left).finiteFibers htor S.property.torsionUnits S.property.pairAdditivity
      L S.obj.hom x hx hn)
    (hvy : v'.val (a.comp g.hom.left) = HarrisNumericalWeilLevel.classOf D C hΦ preservation
      composition unitCoherence associativity comparison symmetry stability square universality
      (D.harrisTaylorReflexStructure C S.obj.hom) compatibility h (a.comp g.hom.left).hom
      (a.comp g.hom.left).finiteFibers htor S.property.torsionUnits S.property.pairAdditivity
      L S.obj.hom y hy hny) :
    letI := auxiliaryStarRing D C
    ∃ (q : ℚˣ) (e : (RationalAlgebraAction.pullback g.hom.left).obj x.1.actionObj ≅
        (RationalAlgebraAction.pullback g.hom.left).obj y.1.actionObj),
      ∃ he : PolarizedWeilLevel.Multiple preservation composition unitCoherence associativity
          comparison symmetry stability square universality W.property.pairAdditivity
          (levelDataBaseChange D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality dualityNaturality
            polarizationStability g.hom.left compatibility h a.hom a.finiteFibers
            (a.comp g.hom.left).finiteFibers htor S.property.torsionUnits
            W.property.torsionUnits (duals g) U x).1
          (levelDataBaseChange D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality dualityNaturality
            polarizationStability g.hom.left compatibility h a.hom a.finiteFibers
            (a.comp g.hom.left).finiteFibers htor S.property.torsionUnits
            W.property.torsionUnits (duals g) U y).1 q e,
        PolarizedWeilLevel.levelIso preservation composition unitCoherence associativity
            comparison symmetry stability square universality compatibility h A
            (D.harrisHodgePELForm C) a.hom a.finiteFibers htor W.property.torsionUnits
            W.property.pairAdditivity
            (levelDataBaseChange D C preservation composition unitCoherence associativity
              comparison symmetry stability square universality dualityNaturality
              polarizationStability g.hom.left compatibility h a.hom a.finiteFibers
              (a.comp g.hom.left).finiteFibers htor S.property.torsionUnits
              W.property.torsionUnits (duals g) U x).1
            (levelDataBaseChange D C preservation composition unitCoherence associativity
              comparison symmetry stability square universality dualityNaturality
              polarizationStability g.hom.left compatibility h a.hom a.finiteFibers
              (a.comp g.hom.left).finiteFibers htor S.property.torsionUnits
              W.property.torsionUnits (duals g) U y).1
            ((hodgeLevelFunctor D C).obj U) q e he
            (levelDataBaseChange D C preservation composition unitCoherence associativity
              comparison symmetry stability square universality dualityNaturality
              polarizationStability g.hom.left compatibility h a.hom a.finiteFibers
              (a.comp g.hom.left).finiteFibers htor S.property.torsionUnits
              W.property.torsionUnits (duals g) U x).2 =
          (levelDataBaseChange D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality dualityNaturality
            polarizationStability g.hom.left compatibility h a.hom a.finiteFibers
            (a.comp g.hom.left).finiteFibers htor S.property.torsionUnits
            W.property.torsionUnits (duals g) U y).2 := by
  let := auxiliaryStarRing D C
  have h1 : (geometricFamilyPointPullback D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor g.hom.left S.obj.hom W.obj.hom (Over.w g.hom)
      S.property.lieNaturality S.property.torsionUnits W.property.torsionUnits (duals g)
      S.property.pairAdditivity W.property.pairAdditivity a).app U (v.val (a.comp g.hom.left)) =
    (geometricFamilyPointPullback D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor g.hom.left S.obj.hom W.obj.hom (Over.w g.hom)
      S.property.lieNaturality S.property.torsionUnits W.property.torsionUnits (duals g)
      S.property.pairAdditivity W.property.pairAdditivity a).app U
      (v'.val (a.comp g.hom.left)) :=
    congrArg (fun w : (tower W).obj U => w.val a) hvv
  rw [hvx, hvy] at h1
  obtain ⟨hx', hn', ex⟩ := geometricFamilyPointPullback_classOf D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor g.hom.left S.obj.hom W.obj.hom
    (Over.w g.hom) S.property.lieNaturality S.property.torsionUnits W.property.torsionUnits
    (duals g) S.property.pairAdditivity W.property.pairAdditivity a x hx hn
  obtain ⟨hy', hny', ey⟩ := geometricFamilyPointPullback_classOf D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor g.hom.left S.obj.hom W.obj.hom
    (Over.w g.hom) S.property.lieNaturality S.property.torsionUnits W.property.torsionUnits
    (duals g) S.property.pairAdditivity W.property.pairAdditivity a y hy hny
  rw [ex, ey] at h1
  exact (HarrisNumericalWeilLevel.classOf_eq_iff D C hΦ preservation composition unitCoherence
    associativity comparison symmetry stability square universality
    (D.harrisTaylorReflexStructure C W.obj.hom) compatibility h a.hom a.finiteFibers htor
    W.property.torsionUnits W.property.pairAdditivity L W.obj.hom
    (levelDataBaseChange D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability g.hom.left compatibility h a.hom a.finiteFibers
      (a.comp g.hom.left).finiteFibers htor S.property.torsionUnits
      W.property.torsionUnits (duals g) U x)
    (levelDataBaseChange D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability g.hom.left compatibility h a.hom a.finiteFibers
      (a.comp g.hom.left).finiteFibers htor S.property.torsionUnits
      W.property.torsionUnits (duals g) U y) hx' hy' hn' hny').mp h1

private abbrev pullRepresentative {S W : Bases} (g : W ⟶ S)
    (a : HarrisGeometricPoint W.obj.left) {U : HarrisLevel D}
    (x : CMData[S, a.comp g.hom.left, U]) : CMData[W, a, U] :=
  levelDataBaseChange D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability g.hom.left compatibility h a.hom a.finiteFibers
    (a.comp g.hom.left).finiteFibers htor S.property.torsionUnits
    W.property.torsionUnits (duals g) U x

local notation "pullRep" => pullRepresentative D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor

/-- A fixed multiplier and isogeny witness the relation on pointed representatives. -/
private abbrev IsPolarizedLevelWitness {S : Bases} (a : HarrisGeometricPoint S.obj.left)
    {U : HarrisLevel D} (x y : CMData[S, a, U]) (q : ℚˣ)
    (e : letI := auxiliaryStarRing D C; x.1.actionObj ≅ y.1.actionObj) : Prop :=
  letI := auxiliaryStarRing D C
  ∃ he : PolarizedWeilLevel.Multiple preservation composition unitCoherence associativity
      comparison symmetry stability square universality S.property.pairAdditivity x.1 y.1 q e,
    PolarizedWeilLevel.levelIso preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h A (D.harrisHodgePELForm C)
      a.hom a.finiteFibers htor S.property.torsionUnits S.property.pairAdditivity
      x.1 y.1 ((hodgeLevelFunctor D C).obj U) q e he x.2 = y.2

local notation "levelWitness" => IsPolarizedLevelWitness D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality compatibility h htor

set_option maxHeartbeats 3200000 in
omit [IsCMField F] [IsScalarTower ℚ F A] in
private theorem transport_pullback_witness {S W : Bases} (g : W ⟶ S)
    (s : HarrisGeometricPoint S.obj.left) (a b : HarrisGeometricPoint W.obj.left)
    {U : HarrisLevel D} (x y : CMData[S, s, U]) (q : ℚˣ)
    (e : letI := auxiliaryStarRing D C
      (RationalAlgebraAction.pullback g.hom.left).obj x.1.actionObj ≅
        (RationalAlgebraAction.pullback g.hom.left).obj y.1.actionObj)
    (he : levelWitness a
      (pullRep g a (rep s (a.comp g.hom.left) x))
      (pullRep g a (rep s (a.comp g.hom.left) y)) q e) :
    levelWitness b
      (pullRep g b (rep s (b.comp g.hom.left) x))
      (pullRep g b (rep s (b.comp g.hom.left) y)) q e := by
  let := auxiliaryStarRing D C
  let ag := a.comp g.hom.left
  let bg := b.comp g.hom.left
  have orbit (z : CMData[S, s, U]) :=
    levelDataBaseChange_pointMapData_snd D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability g.hom.left compatibility h a.finiteFibers b.finiteFibers
      ag.finiteFibers bg.finiteFibers htor S.property.torsionUnits W.property.torsionUnits
      (duals g) s.finiteFibers (pathBetween s ag) (pathBetween s bg) (pathBetween a b) U z
  exact levelDataBaseChange_witness_move D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability g.hom.left compatibility h a.finiteFibers b.finiteFibers
    ag.finiteFibers bg.finiteFibers htor S.property.torsionUnits W.property.torsionUnits
    (duals g) W.property.pairAdditivity (rep s ag x) (rep s ag y)
    (rep s bg x).2 (rep s bg y).2 (pathBetween a b) (orbit x) (orbit y) q e he

local notation "pointEq" => levelDataPointEq D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor

set_option maxHeartbeats 6400000 in
private theorem representative_witness_square
    (geometricFaithfulness : ConnectedGeometricPointHomFaithfulnessStatement.{0})
    {S W W' Z : Bases} (g : W ⟶ S) (g' : W' ⟶ S) (a : Z ⟶ W) (b : Z ⟶ W')
    (hsq : a.hom.left ≫ g.hom.left = b.hom.left ≫ g'.hom.left)
    {U : HarrisLevel D}
    (hRigid : CMGeometricCoarseRigidity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h htor U)
    (s : HarrisGeometricPoint S.obj.left) (x y : CMData[S, s, U])
    (hx : Good[S] x.1) (hn : Numerical[S] x.1) (q q' : ℚˣ) :
    letI := auxiliaryStarRing D C
    ∀ (e : (RationalAlgebraAction.pullback g.hom.left).obj x.1.actionObj ≅
          (RationalAlgebraAction.pullback g.hom.left).obj y.1.actionObj)
      (e' : (RationalAlgebraAction.pullback g'.hom.left).obj x.1.actionObj ≅
          (RationalAlgebraAction.pullback g'.hom.left).obj y.1.actionObj),
      (∀ c : HarrisGeometricPoint W.obj.left, levelWitness c
        (pullRep g c (rep s (c.comp g.hom.left) x))
        (pullRep g c (rep s (c.comp g.hom.left) y)) q e) →
      (∀ c : HarrisGeometricPoint W'.obj.left, levelWitness c
        (pullRep g' c (rep s (c.comp g'.hom.left) x))
        (pullRep g' c (rep s (c.comp g'.hom.left) y)) q' e') →
      (RationalAlgebraAction.pullback a.hom.left).mapIso e ≪≫
          RationalAlgebraAction.pullbackSquareIso g.hom.left g'.hom.left a.hom.left b.hom.left hsq
            y.1.actionObj =
        RationalAlgebraAction.pullbackSquareIso g.hom.left g'.hom.left a.hom.left b.hom.left hsq
            x.1.actionObj ≪≫ (RationalAlgebraAction.pullback b.hom.left).mapIso e' := by
  let := auxiliaryStarRing D C
  intro e e' witness witness'
  let z := Classical.arbitrary (HarrisGeometricPoint Z.obj.left)
  let P := (HarrisGeometricPoint.mk z.Ω (𝟙 _)).comp z.hom
  let Pa := P.comp a.hom.left
  let Pb := P.comp b.hom.left
  let Pag := Pa.comp g.hom.left
  let Pbg := Pb.comp g'.hom.left
  let Pleft := P.comp (a.hom.left ≫ g.hom.left)
  let Pright := P.comp (b.hom.left ≫ g'.hom.left)
  let assocLeft := Category.assoc P.hom a.hom.left g.hom.left
  let assocRight := Category.assoc P.hom b.hom.left g'.hom.left
  let sameComposite := congrArg (fun f => P.hom ≫ f) hsq
  let moveLeft := pointEq S.property.torsionUnits assocLeft
    Pag.finiteFibers Pleft.finiteFibers U
  let moveRight := pointEq S.property.torsionUnits assocRight
    Pbg.finiteFibers Pright.finiteFibers U
  let moveAcross := pointEq S.property.torsionUnits sameComposite
    Pleft.finiteFibers Pright.finiteFibers U
  have moveRep (w : CMData[S, s, U]) :
      moveAcross (moveLeft (rep s Pag w)) = moveRight (rep s Pbg w) := by
    have eLeft : moveLeft (rep s Pag w) = rep s Pleft w :=
      levelDataPointEq_pointMapData D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h htor
        S.property.torsionUnits s.finiteFibers assocLeft Pag.finiteFibers Pleft.finiteFibers
        U (pathBetween s Pag) (pathBetween s Pleft) w
    have eAcross : moveAcross (rep s Pleft w) = rep s Pright w :=
      levelDataPointEq_pointMapData D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h htor
        S.property.torsionUnits s.finiteFibers sameComposite Pleft.finiteFibers Pright.finiteFibers
        U (pathBetween s Pleft) (pathBetween s Pright) w
    have eRight : moveRight (rep s Pbg w) = rep s Pright w :=
      levelDataPointEq_pointMapData D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h htor
        S.property.torsionUnits s.finiteFibers assocRight Pbg.finiteFibers Pright.finiteFibers
        U (pathBetween s Pbg) (pathBetween s Pright) w
    rw [eLeft, eAcross, eRight]
  -- Only the common composite is needed, with the same choices of dual data on both sides.
  let dualOf (c : Z.obj.left ⟶ S.obj.left)
      (X : PositivePolarizedAction D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality (S := S.obj.left)) :
      PositivePullbackDualData D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality c X :=
    Classical.choice
      (Z.property.dualExists ((AbelianScheme.baseChange c).obj X.actionObj.abelianScheme))
  exact pulledWitness_square_compatible D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor S.obj.hom S.property.lieNaturality
    Z.property.lieNaturality S.property.torsionUnits W.property.torsionUnits W'.property.torsionUnits
    Z.property.torsionUnits W.property.pairAdditivity W'.property.pairAdditivity
    Z.property.pairAdditivity g.hom.left g'.hom.left a.hom.left b.hom.left hsq
    (duals g) (duals g') (duals a) (duals b) dualOf z.hom P.finiteFibers Pa.finiteFibers Pb.finiteFibers
    Pag.finiteFibers Pbg.finiteFibers Pleft.finiteFibers Pright.finiteFibers
    geometricFaithfulness hRigid (rep s Pag x) (rep s Pag y) (rep s Pbg x).2 (rep s Pbg y).2
    hx hn (moveRep x) (moveRep y) e e' ⟨q, witness Pa⟩ ⟨q', witness' Pb⟩

set_option maxHeartbeats 3200000 in
private theorem representative_witness_scheme_square
    (geometricFaithfulness : ConnectedGeometricPointHomFaithfulnessStatement.{0})
    {S W W' : Bases} (g : W ⟶ S) (g' : W' ⟶ S)
    (Z : Scheme.{0}) [IsLocallyNoetherian Z] [ConnectedSpace Z]
    (a : Z ⟶ W.obj.left) (b : Z ⟶ W'.obj.left)
    (hsq : a ≫ g.hom.left = b ≫ g'.hom.left)
    {U : HarrisLevel D}
    (hRigid : CMGeometricCoarseRigidity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h htor U)
    (s : HarrisGeometricPoint S.obj.left) (x y : CMData[S, s, U])
    (hx : Good[S] x.1) (hn : Numerical[S] x.1) (q q' : ℚˣ) :
    letI := auxiliaryStarRing D C
    ∀ (e : (RationalAlgebraAction.pullback g.hom.left).obj x.1.actionObj ≅
          (RationalAlgebraAction.pullback g.hom.left).obj y.1.actionObj)
      (e' : (RationalAlgebraAction.pullback g'.hom.left).obj x.1.actionObj ≅
          (RationalAlgebraAction.pullback g'.hom.left).obj y.1.actionObj),
      (∀ c : HarrisGeometricPoint W.obj.left, levelWitness c
        (pullRep g c (rep s (c.comp g.hom.left) x))
        (pullRep g c (rep s (c.comp g.hom.left) y)) q e) →
      (∀ c : HarrisGeometricPoint W'.obj.left, levelWitness c
        (pullRep g' c (rep s (c.comp g'.hom.left) x))
        (pullRep g' c (rep s (c.comp g'.hom.left) y)) q' e') →
      (RationalAlgebraAction.pullback a).mapIso e ≪≫
          RationalAlgebraAction.pullbackSquareIso g.hom.left g'.hom.left a b hsq y.1.actionObj =
        RationalAlgebraAction.pullbackSquareIso g.hom.left g'.hom.left a b hsq x.1.actionObj ≪≫
          (RationalAlgebraAction.pullback b).mapIso e' := by
  let := auxiliaryStarRing D C
  intro e e' witness witness'
  let p := (a ≫ g.hom.left) ≫ S.obj.hom
  have ha : a ≫ W.obj.hom = p := by
    dsimp only [p]
    rw [Category.assoc, Over.w g.hom]
  have hb : b ≫ W'.obj.hom = p := by
    dsimp only [p]
    rw [hsq, Category.assoc, Over.w g'.hom]
  let O : Over (Spec (.of F)) := Over.mk p
  let _ : IsLocallyNoetherian O.left := ‹IsLocallyNoetherian Z›
  let _ : ConnectedSpace O.left := ‹ConnectedSpace Z›
  let Z' : Bases := ⟨O, (admissibleCMBase_iff_dualGeometry D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality O).mpr
    (fun B => ⟨relativeDualSchemeExistence.{0} _ B,
      relativeDualSchemeGeometry.{0} _ B (relativeDualSchemeExistence.{0} _ B)⟩)⟩
  let a' : Z' ⟶ W := ObjectProperty.homMk (Over.homMk a ha)
  let b' : Z' ⟶ W' := ObjectProperty.homMk (Over.homMk b hb)
  exact representative_witness_square D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor geometricFaithfulness
    (S := S) (W := W) (W' := W') (Z := Z') g g' a' b' hsq hRigid s x y hx hn q q' e e'
    witness witness'

set_option maxHeartbeats 3200000 in
private theorem class_eq_of_pullback_witness {S W : Bases} (g : W ⟶ S)
    (a : HarrisGeometricPoint W.obj.left)
    (detectsZero : ∀ (B B' : AbelianScheme S.obj.left) (r : Hom0 B B'),
      rationalBaseChangeHom g.hom.left r = 0 → r = 0)
    {U : HarrisLevel D} (x y : CMData[S, a.comp g.hom.left, U])
    (hx : Good[S] x.1) (hn : Numerical[S] x.1)
    (hy : Good[S] y.1) (hny : Numerical[S] y.1) (q : ℚˣ)
    (e : letI := auxiliaryStarRing D C; x.1.actionObj ≅ y.1.actionObj)
    (hW : levelWitness a (pullRep g a x) (pullRep g a y) q
      ((RationalAlgebraAction.pullback g.hom.left).mapIso e)) :
    classOfAt[S, a.comp g.hom.left] x hx hn = classOfAt[S, a.comp g.hom.left] y hy hny := by
  let := auxiliaryStarRing D C
  let s := a.comp g.hom.left
  obtain ⟨hp, hl⟩ := hW
  have globalMultiple := levelDataBaseChange_multiple_reflect D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability g.hom.left compatibility h a.hom
    a.finiteFibers s.finiteFibers htor S.property.torsionUnits W.property.torsionUnits
    (duals g) S.property.pairAdditivity W.property.pairAdditivity detectsZero x y q e hp
  have globalLevel := levelDataBaseChange_reflect D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability g.hom.left compatibility h a.hom a.finiteFibers s.finiteFibers
    htor S.property.torsionUnits W.property.torsionUnits (duals g) S.property.pairAdditivity
    W.property.pairAdditivity x y q e globalMultiple hp hl
  exact (HarrisNumericalWeilLevel.classOf_eq_iff D C hΦ preservation composition unitCoherence
    associativity comparison symmetry stability square universality
    (D.harrisTaylorReflexStructure C S.obj.hom) compatibility h s.hom s.finiteFibers htor
    S.property.torsionUnits S.property.pairAdditivity L S.obj.hom x y hx hy hn hny).mpr
    ⟨q, e, globalMultiple, globalLevel⟩

set_option maxHeartbeats 6400000 in
/-- For a jointly surjective étale family of connected admissible tests, the
normalized small-level classes have at most one amalgamation, given geometric
Hom faithfulness and étale descent for rational Hom. -/
theorem cmConnectedEtale_separated
    (geometricFaithfulness : ConnectedGeometricPointHomFaithfulnessStatement.{0})
    (rationalDescent : ConnectedEtaleRationalHomDescentStatement.{0}) :
    CMConnectedEtaleSeparatedStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor := by
  classical
  let := auxiliaryStarRing D C
  intro U S K W g het hsurj family v v' hv hv'
  have equalLocally (k : K) : (pull (g k)).app U.obj v = (pull (g k)).app U.obj v' :=
    (hv (g k) (Presieve.ofArrows.mk k)).trans (hv' (g k) (Presieve.ofArrows.mk k)).symm
  obtain ⟨k₀, _, _⟩ := hsurj (Classical.arbitrary S.obj.left)
  let a (k : K) := Classical.arbitrary (HarrisGeometricPoint (W k).obj.left)
  let s := (a k₀).comp (g k₀).hom.left
  obtain ⟨x, hx, hn, hxClass⟩ := HarrisNumericalWeilLevel.classOf_surjective D C hΦ
    preservation composition unitCoherence associativity comparison symmetry stability square
    universality (D.harrisTaylorReflexStructure C S.obj.hom) compatibility h s.hom s.finiteFibers
    htor S.property.torsionUnits S.property.pairAdditivity L S.obj.hom (v.val s)
  obtain ⟨y, hy, hny, hyClass⟩ := HarrisNumericalWeilLevel.classOf_surjective D C hΦ
    preservation composition unitCoherence associativity comparison symmetry stability square
    universality (D.harrisTaylorReflexStructure C S.obj.hom) compatibility h s.hom s.finiteFibers
    htor S.property.torsionUnits S.property.pairAdditivity L S.obj.hom (v'.val s)
  let T (k : K) := (W k).obj.left
  let f (k : K) : T k ⟶ S.obj.left := (g k).hom.left
  let _ : ∀ k, IsLocallyNoetherian (T k) := fun k => (W k).property.locallyNoetherian
  let _ : ∀ k, ConnectedSpace (T k) := fun k => (W k).property.connected
  have classAt (b : HarrisGeometricPoint S.obj.left) :
      v.val b = classOfAt[S, b] (rep s b x) hx hn :=
    classOf_representativeAt D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h htor s b v x hx hn hxClass
  have classAt' (b : HarrisGeometricPoint S.obj.left) :
      v'.val b = classOfAt[S, b] (rep s b y) hy hny :=
    classOf_representativeAt D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h htor s b v' y hy hny hyClass
  have localWitness (k : K) :
      ∃ (q : ℚˣ) (e : (RationalAlgebraAction.pullback (f k)).obj x.1.actionObj ≅
          (RationalAlgebraAction.pullback (f k)).obj y.1.actionObj),
        levelWitness (a k) (pullRep (g k) (a k) (rep s ((a k).comp (f k)) x))
          (pullRep (g k) (a k) (rep s ((a k).comp (f k)) y)) q e := by
    let b := (a k).comp (f k)
    exact witnessAt_of_pullback_eq D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor (g k) v v' (equalLocally k) (a k) (rep s b x) (rep s b y)
      hx hn hy hny (classAt b) (classAt' b)
  choose q e hWitness using localWitness
  have witness (k : K) (b : HarrisGeometricPoint (T k)) :
      levelWitness b (pullRep (g k) b (rep s (b.comp (f k)) x))
        (pullRep (g k) b (rep s (b.comp (f k)) y)) (q k) (e k) :=
    transport_pullback_witness D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality dualityNaturality polarizationStability compatibility
      h htor (g k) s (a k) b x y (q k) (e k) (hWitness k)
  have rigid := (cmSmallLevelRigidity D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality compatibility h htor) U.obj U.property
  have squareCompat (k l : K) (Z : Scheme.{0}) [IsLocallyNoetherian Z] [ConnectedSpace Z]
      (b : Z ⟶ T k) (c : Z ⟶ T l) (hsq : b ≫ f k = c ≫ f l) :
      (RationalAlgebraAction.pullback b).mapIso (e k) ≪≫
          RationalAlgebraAction.pullbackSquareIso (f k) (f l) b c hsq y.1.actionObj =
        RationalAlgebraAction.pullbackSquareIso (f k) (f l) b c hsq x.1.actionObj ≪≫
          (RationalAlgebraAction.pullback c).mapIso (e l) := by
    exact representative_witness_scheme_square D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor geometricFaithfulness
      (S := S) (W := W k) (W' := W l) (g k) (g l) Z b c hsq rigid s x y hx hn
      (q k) (q l) (e k) (e l) (witness k) (witness l)
  have hinj := rationalBaseChangeHom_injective_of_geometricPoint geometricFaithfulness
    S.property.torsionUnits (f k₀) (a k₀).hom
  obtain ⟨iso, hi⟩ := RationalAlgebraAction.exists_iso_of_etale_rationalHomDescent
    rationalDescent S.property.torsionUnits T f het hsurj k₀ hinj
    (X := x.1.actionObj) (Y := y.1.actionObj) e squareCompat
  let x' := rep s s x
  let y' := rep s s y
  have atPiece : levelWitness (a k₀) (pullRep (g k₀) (a k₀) x') (pullRep (g k₀) (a k₀) y')
      (q k₀) ((RationalAlgebraAction.pullback (f k₀)).mapIso iso) :=
    (congrArg (levelWitness (a k₀) (pullRep (g k₀) (a k₀) x') (pullRep (g k₀) (a k₀) y')
      (q k₀)) (hi k₀)).mpr (hWitness k₀)
  have detectsZero (B B' : AbelianScheme S.obj.left) (r : Hom0 B B')
      (hr : rationalBaseChangeHom (f k₀) r = 0) : r = 0 :=
    hinj B B' (hr.trans (map_zero (rationalBaseChangeHom (f k₀))).symm)
  have sameClass : classOfAt[S, s] x' hx hn = classOfAt[S, s] y' hy hny :=
    class_eq_of_pullback_witness D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality dualityNaturality polarizationStability compatibility
      h htor (S := S) (W := W k₀) (g k₀) (a k₀) detectsZero x' y' hx hn hy hny (q k₀) iso atPiece
  exact (geometricFamilyEvaluationEquiv D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality S.obj.hom compatibility h htor
    S.property.torsionUnits S.property.pairAdditivity s U.obj).injective
    ((classAt s).trans (sameClass.trans (classAt' s).symm))

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
