import Langlands.Shimura.PEL.HarrisTaylorCMCompactRepresentatives
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedUnpointedPresheaf

/-! # Integral comparison of compact Tate-normalized representatives -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AbelianScheme.PolarizedFiniteLevel
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
  (P : Prerequisites.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "Bases" => AdmissibleCMBaseCategory D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
local notation "BaseProperty" Z:max => AdmissibleCMBase D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  (Z).obj
local notation "baseProperty" Z:max => ((Z).property : BaseProperty Z)
local notation "Good" Z:max => PositiveObjectCondition D C hΦ P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  P.square P.universality (D.harrisTaylorReflexStructure C (Z).obj.hom)
local notation "Numerical" Z:max => HarrisNumericalWeilLevel.NumericalObjectCondition D C
  P.preservation P.composition P.unitCoherence P.associativity P.comparison P.symmetry
  P.stability P.square P.universality L (Z).obj.hom
local notation "classOfAt[" Z ", " a ", " U "]" => HarrisNumericalWeilLevel.classOf D C hΦ
  P.preservation P.composition P.unitCoherence P.associativity P.comparison P.symmetry
  P.stability P.square P.universality (D.harrisTaylorReflexStructure C (Z).obj.hom)
  compatibility h (a).hom (a).finiteFibers htor (baseProperty Z).torsionUnits
  (baseProperty Z).pairAdditivity L (Z).obj.hom (U := U)
local notation "classesAt[" Z ", " a "]" => geometricClassTower D C P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  P.square P.universality (Z).obj.hom compatibility h htor (baseProperty Z).torsionUnits
  (baseProperty Z).pairAdditivity a
local notation "tower" => unpointedClassTower D C P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability P.square P.universality compatibility h htor
local notation "fibreAt" a:max => fiberFunctor (HarrisGeometricPoint.hom a)
  (HarrisGeometricPoint.finiteFibers a)

local notation "Rep" => CompactTateCMRepresentative D C P compatibility h htor
local notation "moveData[" S "]" => HarrisTaylorLieWeilLevel.pointMapRepresentative D C
  P.preservation P.composition P.unitCoherence P.associativity P.comparison P.symmetry
  P.stability P.square P.universality compatibility h htor (baseProperty S).torsionUnits

set_option maxHeartbeats 2400000 in
/-- The pointed class of a representative with compact Tate normalization. -/
def CompactTateCMRepresentative.pointedClass {S : Bases} {a : HarrisGeometricPoint S.obj.left}
    {U : HarrisLevel D} (x : Rep S a U) : (classesAt[S, a]).obj U :=
  classOfAt[S, a, U] x.data x.good x.numerical

local notation "mkClass" => CompactTateCMRepresentative.pointedClass D C P compatibility h htor

/-- Transport a representative to another point of the same connected test. -/
def CompactTateCMRepresentative.pointMap {S : Bases} {a b : HarrisGeometricPoint S.obj.left}
    {U : HarrisLevel D} (x : Rep S a U) (p : fibreAt a ≅ fibreAt b) :
    Rep S b U where
  data := moveData[S] p U x.data
  good := x.good
  numerical := x.numerical
  normalized := compactTateCMPointMap_normalized D C P compatibility h htor x p

local notation "move" => CompactTateCMRepresentative.pointMap D C P compatibility h htor

/-- Point transport preserves the represented compatible geometric family. -/
theorem CompactTateCMRepresentative.pointMap_class {S : Bases}
    {a b : HarrisGeometricPoint S.obj.left} {U : HarrisLevel D}
    (x : Rep S a U) (v : (tower S).obj U)
    (hx : mkClass x = v.val a) (p : fibreAt a ≅ fibreAt b) :
    mkClass (move x p) = v.val b :=
  compactTateCMPointMap_pointedClass D C P compatibility h htor x v hx p

variable (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})

local notation "duals" => unpointedPullbackDualData D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
local notation "pull" => unpointedClassTowerPullback D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  dualityNaturality polarizationStability compatibility h htor

local notation "pointOver" z:max f:max => HarrisGeometricPoint.comp z (f).hom.left
local notation "pullData[" R ", " S ", " f ", " z ", " U "]" =>
  levelDataBaseChange D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  dualityNaturality polarizationStability (f).hom.left compatibility h (z).hom (z).finiteFibers
  (pointOver z f).finiteFibers htor (baseProperty S).torsionUnits (baseProperty R).torsionUnits
  (duals f) U

set_option maxHeartbeats 2400000 in
private theorem pullData_conditions {R S : Bases} {U : HarrisLevel D}
    (f : R ⟶ S) (z : HarrisGeometricPoint R.obj.left) (x : Rep S (pointOver z f) U) :
    ∃ (hx : (Good R) (pullData[R, S, f, z, U] x.data).1)
      (hn : (Numerical R) (pullData[R, S, f, z, U] x.data).1),
      ∀ (v : (tower S).obj U), mkClass x = v.val (pointOver z f) →
        classOfAt[R, z, U] (pullData[R, S, f, z, U] x.data) hx hn = ((pull f).app U v).val z := by
  obtain ⟨hx, hn, hEq⟩ := geometricFamilyPointPullback_classOf D C P.preservation
    P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
    P.universality dualityNaturality polarizationStability compatibility h htor f.hom.left
    S.obj.hom R.obj.hom (Over.w f.hom) (baseProperty S).lieNaturality
    (baseProperty S).torsionUnits (baseProperty R).torsionUnits (duals f)
    (baseProperty S).pairAdditivity (baseProperty R).pairAdditivity z x.data x.good x.numerical
  refine ⟨hx, hn, fun v hv => hEq.symm.trans ?_⟩
  exact congrArg (fun w => (geometricFamilyPointPullback D C P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
    dualityNaturality polarizationStability compatibility h htor f.hom.left S.obj.hom R.obj.hom
    (Over.w f.hom) (baseProperty S).lieNaturality (baseProperty S).torsionUnits
    (baseProperty R).torsionUnits (duals f) (baseProperty S).pairAdditivity
    (baseProperty R).pairAdditivity z).app U w) hv

set_option maxHeartbeats 2400000 in
/-- Pull back the representative on the actual pulled-back polarized abelian
scheme, with the original pullback of its level orbit. -/
def CompactTateCMRepresentative.pullback {R S : Bases} {U : HarrisLevel D}
    (f : R ⟶ S) (z : HarrisGeometricPoint R.obj.left) (x : Rep S (pointOver z f) U) : Rep R z U :=
  let hx := pullData_conditions D C P compatibility h htor dualityNaturality polarizationStability f z x
  { data := pullData[R, S, f, z, U] x.data
    good := hx.choose
    numerical := hx.choose_spec.choose
    normalized := (harrisCompactOrbitLatticeCondition_levelDataBaseChange D C P compatibility h
      dualityNaturality polarizationStability f.hom.left z.hom z.finiteFibers (pointOver z f).finiteFibers
      htor (baseProperty S).torsionUnits (baseProperty R).torsionUnits (duals f) U x.data).mpr
        x.normalized }

local notation "pullRep" => CompactTateCMRepresentative.pullback D C P compatibility h htor
  dualityNaturality polarizationStability

/-- The pulled-back normalized representative gives the pointed class of the
pulled-back compatible family. -/
theorem CompactTateCMRepresentative.pullback_class {R S : Bases} {U : HarrisLevel D}
    (f : R ⟶ S) (z : HarrisGeometricPoint R.obj.left)
    (x : Rep S (pointOver z f) U) (v : (tower S).obj U)
    (hx : mkClass x = v.val (pointOver z f)) :
    mkClass (pullRep f z x) = ((pull f).app U v).val z :=
  ((pullData_conditions D C P compatibility h htor dualityNaturality polarizationStability
    f z x).choose_spec.choose_spec) v hx

local notation "ActIso" X:max Y:max => letI := auxiliaryStarRing D C; (X).actionObj ≅ (Y).actionObj
local notation "ab" X:max => letI := auxiliaryStarRing D C; (X).actionObj.abelianScheme
local notation "multipleAt[" R "]" => PolarizedWeilLevel.Multiple P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  (baseProperty R).pairAdditivity
local notation "levelIsoAt[" R ", " z "]" => PolarizedWeilLevel.levelIso P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h A (D.harrisHodgePELForm C) (z).hom (z).finiteFibers htor
  (baseProperty R).torsionUnits (baseProperty R).pairAdditivity

set_option maxHeartbeats 3200000 in
/-- An actual abelian-scheme isomorphism lifting a polarized, equivariant
rational level witness between compact Tate-normalized representatives. -/
structure CompactTateCMWitness {R : Bases} {U : HarrisLevel D}
    (z : HarrisGeometricPoint R.obj.left) (x y : Rep R z U) where
  multiplier : ℚˣ
  rationalIso : ActIso x.data.1 y.data.1
  polarization : letI := auxiliaryStarRing D C
    multipleAt[R] x.data.1 y.data.1 multiplier rationalIso
  level : letI := auxiliaryStarRing D C
    levelIsoAt[R, z] x.data.1 y.data.1 ((hodgeLevelFunctor D C).obj U) multiplier rationalIso
      polarization x.data.2 = y.data.2
  integralIso : ab x.data.1 ≅ ab y.data.1
  hom_eq : letI := auxiliaryStarRing D C
    Rationalization.ofHom integralIso.hom = RationalAlgebraAction.hom0 rationalIso.hom
  inv_eq : letI := auxiliaryStarRing D C
    Rationalization.ofHom integralIso.inv = RationalAlgebraAction.hom0 rationalIso.inv

local notation "Witness" => CompactTateCMWitness D C P compatibility h htor

set_option maxHeartbeats 2400000 in
/-- Equality of pointed classes of compact Tate-normalized representatives
admits an actual isomorphism lifting the witness of the class relation. -/
theorem nonempty_compactTateCMWitness {R : Bases} {U : HarrisLevel D}
    (z : HarrisGeometricPoint R.obj.left) (x y : Rep R z U) (he : mkClass x = mkClass y) :
    Nonempty (Witness z x y) := by
  let := auxiliaryStarRing D C
  let := harrisCMGeometricPoint_charZero D C P R z
  obtain ⟨q, e, he, hl⟩ := (HarrisNumericalWeilLevel.classOf_eq_iff D C hΦ P.preservation
    P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
    P.universality (D.harrisTaylorReflexStructure C R.obj.hom) compatibility h z.hom z.finiteFibers
    htor (baseProperty R).torsionUnits (baseProperty R).pairAdditivity L R.obj.hom x.data y.data
    x.good y.good x.numerical y.numerical).mp he
  obtain ⟨g, hh, hi⟩ := harrisCompactTateNormalized_iso_integral D C P R compatibility h
    z.hom z.finiteFibers htor x.data y.data x.normalized y.normalized q e he hl
  exact ⟨⟨q, e, he, hl, g, hh, hi⟩⟩

local notation "pathBetween" p:max q:max =>
  Classical.choice (geometricPathExists (HarrisGeometricPoint.hom p) (HarrisGeometricPoint.hom q)
    (HarrisGeometricPoint.finiteFibers p) (HarrisGeometricPoint.finiteFibers q))

set_option maxHeartbeats 2400000 in
/-- Compare two normalized representatives of local classes on a common
connected test where the pulled-back classes agree. -/
theorem nonempty_compactTateCMWitness_overlap
    {R S T : Bases} {U : HarrisLevel D} {a : HarrisGeometricPoint S.obj.left}
    (f : R ⟶ S) (z : HarrisGeometricPoint R.obj.left) (g : R ⟶ T)
    (b : HarrisGeometricPoint T.obj.left) (x : Rep S a U) (y : Rep T b U)
    (v : (tower S).obj U) (w : (tower T).obj U) (hx : mkClass x = v.val a)
    (hy : mkClass y = w.val b) (he : (pull f).app U v = (pull g).app U w) :
    Nonempty (Witness z (pullRep f z (move x (pathBetween a (pointOver z f))))
      (pullRep g z (move y (pathBetween b (z.comp g.hom.left))))) := by
  let x' := move x (pathBetween a (pointOver z f))
  let y' := move y (pathBetween b (z.comp g.hom.left))
  have hv := CompactTateCMRepresentative.pointMap_class D C P compatibility h htor x v hx
    (pathBetween a (pointOver z f))
  have hw := CompactTateCMRepresentative.pointMap_class D C P compatibility h htor y w hy
    (pathBetween b (z.comp g.hom.left))
  have hp := CompactTateCMRepresentative.pullback_class D C P compatibility h htor
    dualityNaturality polarizationStability f z x' v hv
  have hq := CompactTateCMRepresentative.pullback_class D C P compatibility h htor
    dualityNaturality polarizationStability g z y' w hw
  exact nonempty_compactTateCMWitness D C P compatibility h htor z (pullRep f z x')
    (pullRep g z y') (hp.trans ((congrArg (fun u : (tower R).obj U => u.val z) he).trans hq.symm))

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
