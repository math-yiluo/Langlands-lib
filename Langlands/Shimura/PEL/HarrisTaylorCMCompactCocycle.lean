import Langlands.Shimura.PEL.HarrisTaylorCMCompactOverlap
import Langlands.Shimura.PEL.HarrisTaylorCMConnectedRigidity
import Langlands.Shimura.PEL.HarrisTaylorCMWitnessTransport
import Langlands.Shimura.PEL.PolarizedWeilLevelWitness

/-! # Compatibility of integral Harris CM witnesses on connected tests -/

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
variable (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})

local notation "duals" => unpointedPullbackDualData D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
local notation "pointOver" z:max f:max => HarrisGeometricPoint.comp z (f).hom.left
local notation "pullData[" R ", " S ", " f ", " z ", " U "]" =>
  levelDataBaseChange D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  dualityNaturality polarizationStability (f).hom.left compatibility h (z).hom (z).finiteFibers
  (pointOver z f).finiteFibers htor (baseProperty S).torsionUnits (baseProperty R).torsionUnits
  (duals f) U

local notation "ActIso" X:max Y:max => letI := auxiliaryStarRing D C; (X).actionObj ≅ (Y).actionObj
local notation "ab" X:max => letI := auxiliaryStarRing D C; (X).actionObj.abelianScheme
local notation "pathBetween" p:max q:max =>
  Classical.choice (geometricPathExists (HarrisGeometricPoint.hom p) (HarrisGeometricPoint.hom q)
    (HarrisGeometricPoint.finiteFibers p) (HarrisGeometricPoint.finiteFibers q))

local notation "Rep" => CompactTateCMRepresentative D C P compatibility h htor
local notation "Witness" => CompactTateCMWitness D C P compatibility h htor
local notation "move" => CompactTateCMRepresentative.pointMap D C P compatibility h htor
local notation "pullRep" => CompactTateCMRepresentative.pullback D C P compatibility h htor
  dualityNaturality polarizationStability
local notation "fibreAt" a:max => fiberFunctor (HarrisGeometricPoint.hom a)
  (HarrisGeometricPoint.finiteFibers a)
local notation "pointMove[" R "]" => PolarizedWeilLevel.pointMapData P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  P.square P.universality compatibility h A (D.harrisHodgePELForm C) htor
  (baseProperty R).torsionUnits
local notation "levelIsoAt[" R ", " z "]" => PolarizedWeilLevel.levelIso P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality compatibility h A (D.harrisHodgePELForm C) (z).hom (z).finiteFibers htor
  (baseProperty R).torsionUnits (baseProperty R).pairAdditivity
local notation "indexAt" U:max => ((hodgeLevelFunctor D C).obj U)

/-- Pull back a representative after transporting its orbit to the image of
the new geometric point. The polarized object uses the actual pullback. -/
abbrev CompactTateCMRepresentative.pullbackAt {R S : Bases} {U : HarrisLevel D}
    {a : HarrisGeometricPoint S.obj.left} (f : R ⟶ S) (z : HarrisGeometricPoint R.obj.left)
    (x : Rep S a U) : Rep R z U :=
  pullRep f z (move x (pathBetween a (pointOver z f)))

local notation "pullAt" => CompactTateCMRepresentative.pullbackAt D C P compatibility h htor
  dualityNaturality polarizationStability

set_option maxHeartbeats 3200000 in
/-- Moving the point of a common connected test keeps the same polarized
rational witness and the same lifting isomorphism. -/
def CompactTateCMWitness.atPoint {R S T : Bases} {U : HarrisLevel D}
    {a : HarrisGeometricPoint S.obj.left} {b : HarrisGeometricPoint T.obj.left}
    (f : R ⟶ S) (g : R ⟶ T) (z w : HarrisGeometricPoint R.obj.left)
    (x : Rep S a U) (y : Rep T b U)
    (e : Witness z (pullAt f z x) (pullAt g z y)) :
    Witness w (pullAt f w x) (pullAt g w y) := by
  let := auxiliaryStarRing D C
  let p : fibreAt z ≅ fibreAt w := pathBetween z w
  let xz := pullAt f z x
  let yz := pullAt g z y
  let xw := pullAt f w x
  let yw := pullAt g w y
  have hx : xw.data.2 = (pointMove[R] p (indexAt U) xz.data).2 :=
    levelDataBaseChange_pointMapData_snd D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      dualityNaturality polarizationStability f.hom.left compatibility h z.finiteFibers
      w.finiteFibers (pointOver z f).finiteFibers (pointOver w f).finiteFibers htor
      (baseProperty S).torsionUnits (baseProperty R).torsionUnits (duals f) a.finiteFibers
      (pathBetween a (pointOver z f)) (pathBetween a (pointOver w f)) p U x.data
  have hy : yw.data.2 = (pointMove[R] p (indexAt U) yz.data).2 :=
    levelDataBaseChange_pointMapData_snd D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      dualityNaturality polarizationStability g.hom.left compatibility h z.finiteFibers
      w.finiteFibers (pointOver z g).finiteFibers (pointOver w g).finiteFibers htor
      (baseProperty T).torsionUnits (baseProperty R).torsionUnits (duals g) b.finiteFibers
      (pathBetween b (pointOver z g)) (pathBetween b (pointOver w g)) p U y.data
  have hm := PolarizedWeilLevel.pointMapData_witness P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality compatibility h A
    (D.harrisHodgePELForm C) htor (baseProperty R).torsionUnits (baseProperty R).pairAdditivity
    p (indexAt U) xz.data yz.data e.multiplier e.rationalIso e.polarization e.level
  refine ⟨e.multiplier, e.rationalIso, e.polarization, ?_, e.integralIso, e.hom_eq, e.inv_eq⟩
  exact (congrArg (levelIsoAt[R, w] xw.data.1 yw.data.1 (indexAt U) e.multiplier
    e.rationalIso e.polarization) hx).trans (hm.trans hy.symm)

set_option maxHeartbeats 3200000 in
/-- Pull back a witness when the starting point is the image of the new point. -/
def CompactTateCMWitness.pullback {Z R : Bases} {U : HarrisLevel D}
    (k : Z ⟶ R) (z : HarrisGeometricPoint Z.obj.left) (x y : Rep R (pointOver z k) U)
    (e : Witness (pointOver z k) x y) : Witness z (pullRep k z x) (pullRep k z y) := by
  let := auxiliaryStarRing D C
  let e' := (RationalAlgebraAction.pullback k.hom.left).mapIso e.rationalIso
  let E' := (AbelianScheme.baseChange k.hom.left).mapIso e.integralIso
  have hb := levelDataBaseChange_witness D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    dualityNaturality polarizationStability k.hom.left compatibility h z.hom z.finiteFibers
    (pointOver z k).finiteFibers htor (baseProperty R).torsionUnits (baseProperty Z).torsionUnits
    (duals k) (baseProperty R).pairAdditivity (baseProperty Z).pairAdditivity
    x.data y.data e.multiplier e.rationalIso e.polarization e.level
  refine ⟨e.multiplier, e', hb.choose, hb.choose_spec, E', ?_, ?_⟩
  · change Rationalization.ofHom ((AbelianScheme.baseChange k.hom.left).map e.integralIso.hom) =
      rationalBaseChangeHom k.hom.left (RationalAlgebraAction.hom0 e.rationalIso.hom)
    exact (rationalBaseChangeHom_ofHom k.hom.left e.integralIso.hom).symm.trans
      (congrArg (rationalBaseChangeHom k.hom.left) e.hom_eq)
  · change Rationalization.ofHom ((AbelianScheme.baseChange k.hom.left).map e.integralIso.inv) =
      rationalBaseChangeHom k.hom.left (RationalAlgebraAction.hom0 e.rationalIso.inv)
    exact (rationalBaseChangeHom_ofHom k.hom.left e.integralIso.inv).symm.trans
      (congrArg (rationalBaseChangeHom k.hom.left) e.inv_eq)

set_option maxHeartbeats 3200000 in
/-- The rational and integral parts of a composite witness compose in their
respective categories, with the product multiplier. -/
def CompactTateCMWitness.trans {R : Bases} {U : HarrisLevel D}
    (a : HarrisGeometricPoint R.obj.left) (x y z : Rep R a U)
    (e : Witness a x y) (f : Witness a y z) : Witness a x z := by
  let := auxiliaryStarRing D C
  let q := e.multiplier * f.multiplier
  let i := e.rationalIso ≪≫ f.rationalIso
  let j := e.integralIso ≪≫ f.integralIso
  have hw := PolarizedWeilLevel.witness_trans P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality compatibility h A
    (D.harrisHodgePELForm C) a.hom a.finiteFibers htor (baseProperty R).torsionUnits
    (baseProperty R).pairAdditivity (K := indexAt U) (x := x.data) (y := y.data) (z := z.data)
    (q := e.multiplier) (r := f.multiplier) (e := e.rationalIso) (f := f.rationalIso)
    ⟨e.polarization, e.level⟩ ⟨f.polarization, f.level⟩
  refine ⟨q, i, hw.choose, hw.choose_spec, j, ?_, ?_⟩
  · exact (comp0_homToHom0 e.integralIso.hom f.integralIso.hom).symm.trans
      (congrArg₂ (fun r t => comp0 (ab x.data.1) (ab y.data.1) (ab z.data.1) r t)
        e.hom_eq f.hom_eq)
  · exact (comp0_homToHom0 f.integralIso.inv e.integralIso.inv).symm.trans
      (congrArg₂ (fun r t => comp0 (ab z.data.1) (ab y.data.1) (ab x.data.1) r t)
        f.inv_eq e.inv_eq)

set_option maxHeartbeats 2400000 in
/-- A witness reverses the rational and integral isomorphisms and inverts the multiplier. -/
def CompactTateCMWitness.symm {R : Bases} {U : HarrisLevel D}
    (a : HarrisGeometricPoint R.obj.left) (x y : Rep R a U)
    (e : Witness a x y) : Witness a y x := by
  let := auxiliaryStarRing D C
  have hw := PolarizedWeilLevel.witness_symm P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality compatibility h A
    (D.harrisHodgePELForm C) a.hom a.finiteFibers htor (baseProperty R).torsionUnits
    (baseProperty R).pairAdditivity (K := indexAt U) (x := x.data) (y := y.data)
    (q := e.multiplier) (e := e.rationalIso) ⟨e.polarization, e.level⟩
  exact ⟨e.multiplier⁻¹, e.rationalIso.symm, hw.choose, hw.choose_spec, e.integralIso.symm,
    e.inv_eq, e.hom_eq⟩

local notation "identityComp" a:max =>
  (HarrisGeometricPoint.mk (HarrisGeometricPoint.Ω a) (𝟙 _)).comp (HarrisGeometricPoint.hom a)

set_option maxHeartbeats 3200000 in
include dualityNaturality polarizationStability in
/-- Small-level geometric rigidity forces equality of the integral lifting
isomorphisms between two fixed representatives. -/
theorem CompactTateCMWitness.integralIso_eq {R : Bases} {U : HarrisLevel D}
    (G0 : ConnectedGeometricPointHomFaithfulnessStatement.{0})
    (hRigid : CMGeometricCoarseRigidity D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      compatibility h htor U)
    (a : HarrisGeometricPoint R.obj.left) (x y : Rep R (identityComp a) U)
    (e f : Witness (identityComp a) x y) : e.integralIso = f.integralIso := by
  let := auxiliaryStarRing D C
  have hr := witness_eq_of_geometricRigidity D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    dualityNaturality polarizationStability compatibility h htor G0 hRigid R.obj.hom
    (baseProperty R).lieNaturality (baseProperty R).torsionUnits (baseProperty R).pairAdditivity
    a.hom (identityComp a).finiteFibers x.data y.data x.good x.numerical
    e.multiplier f.multiplier e.rationalIso f.rationalIso e.polarization f.polarization e.level f.level
  apply Iso.ext
  apply Tate.ofHom_injective (baseProperty R).torsionUnits (ab x.data.1) (ab y.data.1)
  exact e.hom_eq.trans ((congrArg (fun i => RationalAlgebraAction.hom0 i.hom) hr).trans f.hom_eq.symm)

local notation "pointEq[" S "]" => levelDataPointEq D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h htor (baseProperty S).torsionUnits

set_option maxHeartbeats 6400000 in
/-- The canonical direct-to-successive pullback comparison is an integral
witness with multiplier one. -/
def CompactTateCMRepresentative.pullbackAtCompWitness {Z R S : Bases} {U : HarrisLevel D}
    {a : HarrisGeometricPoint S.obj.left} (k : Z ⟶ R) (f : R ⟶ S)
    (z : HarrisGeometricPoint Z.obj.left) (x : Rep S a U) :
    Witness z (pullAt (k ≫ f) z x) (pullRep k z (pullAt f (pointOver z k) x)) := by
  let := auxiliaryStarRing D C
  let zk := pointOver z k
  let zkf := pointOver zk f
  let zd := pointOver z (k ≫ f)
  let assoc : zkf.hom = zd.hom := Category.assoc z.hom k.hom.left f.hom.left
  let w := move x (pathBetween a zkf)
  let w' := move x (pathBetween a zd)
  have hw : pointEq[S] assoc zkf.finiteFibers zd.finiteFibers U w.data = w'.data :=
    levelDataPointEq_pointMapData D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      compatibility h htor (baseProperty S).torsionUnits a.finiteFibers assoc
      zkf.finiteFibers zd.finiteFibers U (pathBetween a zkf) (pathBetween a zd) x.data
  let i := RationalAlgebraAction.pullbackCompIso f.hom.left k.hom.left x.data.1.actionObj
  let j := AbelianScheme.baseChangeCompIso f.hom.left k.hom.left (ab x.data.1)
  have hm := levelDataBaseChange_comp_multiple D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    dualityNaturality polarizationStability f.hom.left k.hom.left compatibility h z.hom
    z.finiteFibers zk.finiteFibers zkf.finiteFibers zd.finiteFibers htor
    (baseProperty S).torsionUnits (baseProperty R).torsionUnits (baseProperty Z).torsionUnits
    (duals f) (duals k) (duals (k ≫ f)) (baseProperty Z).pairAdditivity U w.data
  have hl := levelDataBaseChange_comp_witness D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    dualityNaturality polarizationStability f.hom.left k.hom.left compatibility h z.hom
    z.finiteFibers zk.finiteFibers zkf.finiteFibers zd.finiteFibers htor
    (baseProperty S).torsionUnits (baseProperty R).torsionUnits (baseProperty Z).torsionUnits
    (duals f) (duals k) (duals (k ≫ f)) (baseProperty Z).pairAdditivity U w.data
  let direct := pullAt (k ≫ f) z x
  let successive := pullRep k z (pullAt f zk x)
  refine ⟨1, i, hm, ?_, j, rfl, rfl⟩
  have ho : (pullData[Z, S, k ≫ f, z, U]
      (pointEq[S] assoc zkf.finiteFibers zd.finiteFibers U w.data)).2 = direct.data.2 := by
    have he := congrArg (pullData[Z, S, k ≫ f, z, U]) hw
    exact eq_of_heq (Sigma.ext_iff.mp he).2
  exact (congrArg (levelIsoAt[Z, z] direct.data.1 successive.data.1 (indexAt U) 1 i hm)
    ho.symm).trans hl

set_option maxHeartbeats 4800000 in
/-- Pulling back the integral isomorphism of a witness to a common connected test
agrees with the witness on that test under the canonical comparisons. -/
theorem CompactTateCMWitness.integralIso_pullbackAt {Z R S T : Bases} {U : HarrisLevel D}
    (G0 : ConnectedGeometricPointHomFaithfulnessStatement.{0})
    (hRigid : CMGeometricCoarseRigidity D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      compatibility h htor U)
    {a : HarrisGeometricPoint S.obj.left} {b : HarrisGeometricPoint T.obj.left}
    (k : Z ⟶ R) (f : R ⟶ S) (g : R ⟶ T)
    (z : HarrisGeometricPoint R.obj.left) (c : HarrisGeometricPoint Z.obj.left)
    (x : Rep S a U) (y : Rep T b U)
    (e : Witness z (pullAt f z x) (pullAt g z y))
    (e' : Witness (identityComp c) (pullAt (k ≫ f) (identityComp c) x)
      (pullAt (k ≫ g) (identityComp c) y)) :
    AbelianScheme.baseChangeCompIso f.hom.left k.hom.left (ab x.data.1) ≪≫
      ((AbelianScheme.baseChange k.hom.left).mapIso e.integralIso ≪≫
        (AbelianScheme.baseChangeCompIso g.hom.left k.hom.left (ab y.data.1)).symm) =
      e'.integralIso := by
  let u := identityComp c
  let uk := pointOver u k
  let x' := pullAt f uk x
  let y' := pullAt g uk y
  let xd := pullAt (k ≫ f) u x
  let yd := pullAt (k ≫ g) u y
  let xs := pullRep k u x'
  let ys := pullRep k u y'
  let moved := CompactTateCMWitness.atPoint D C P compatibility h htor dualityNaturality
    polarizationStability f g z uk x y e
  let pulled := CompactTateCMWitness.pullback D C P compatibility h htor dualityNaturality
    polarizationStability k u x' y' moved
  let left := CompactTateCMRepresentative.pullbackAtCompWitness D C P compatibility h htor
    dualityNaturality polarizationStability k f u x
  let right := CompactTateCMRepresentative.pullbackAtCompWitness D C P compatibility h htor
    dualityNaturality polarizationStability k g u y
  let er := CompactTateCMWitness.symm D C P compatibility h htor u yd ys right
  let mid := CompactTateCMWitness.trans D C P compatibility h htor u xs ys yd pulled er
  let full := CompactTateCMWitness.trans D C P compatibility h htor u xd xs yd left mid
  exact CompactTateCMWitness.integralIso_eq D C P compatibility h htor dualityNaturality
    polarizationStability G0 hRigid c xd yd full e'

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
