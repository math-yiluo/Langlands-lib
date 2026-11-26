import Langlands.Shimura.PEL.HarrisTaylorCMSchemeLevels

/-! # The universal CM class and its actual representatives on connected components -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000

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

open Langlands.AlgebraicGeometry

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀

/-! ### Pointwise pullback of an actual representative -/

section PointPullback
variable {S T : Scheme.{0}}
  [QuasiSeparatedSpace S] [QuasiSeparatedSpace T]
  [ConnectedSpace S] [ConnectedSpace T]
  [IsLocallyNoetherian S] [IsLocallyNoetherian T]
  (b : T ⟶ S) (p : S ⟶ Spec (.of F)) (q : T ⟶ Spec (.of F))
  (hp : b ≫ p = q)
  (lieS : LieBaseChangeNaturalityStatement S)
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T k.val).X.hom]
  [hμetT : ∀ k : Index (fun _ => True), Etale (mu T k.val).X.hom]
  (dualData : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality b X)
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (addT : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T))

omit [ConnectedSpace S] [ConnectedSpace T] [IsLocallyNoetherian S] [IsLocallyNoetherian T] in
/-- At an actual geometric point, the existing pointed pullback sends the class of an
actual representative to the class of that representative's actual base change. -/
theorem geometricFamilyPointPullback_classOf (a : HarrisGeometricPoint T) {U : HarrisLevel D}
    (x : HarrisLevelData D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h (a.comp b).hom
      (a.comp b).finiteFibers htor huS U)
    (hx : PositiveObjectCondition D C hΦ preservation composition unitCoherence associativity
      comparison symmetry stability square universality (D.harrisTaylorReflexStructure C p) x.1)
    (hn : HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality L p x.1) :
    ∃ (hx' : PositiveObjectCondition D C hΦ preservation composition unitCoherence
        associativity comparison symmetry stability square universality
        (D.harrisTaylorReflexStructure C q)
        (levelDataBaseChange D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability b compatibility h a.hom a.finiteFibers (a.comp b).finiteFibers
          htor huS huT dualData U x).1)
      (hn' : HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality L q
        (levelDataBaseChange D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability b compatibility h a.hom a.finiteFibers (a.comp b).finiteFibers
          htor huS huT dualData U x).1),
      (geometricFamilyPointPullback D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor b p q hp lieS huS huT dualData
        addS addT a).app U
        (HarrisNumericalWeilLevel.classOf D C hΦ preservation composition unitCoherence
          associativity comparison symmetry stability square universality
          (D.harrisTaylorReflexStructure C p) compatibility h (a.comp b).hom
          (a.comp b).finiteFibers htor huS addS L p x hx hn) =
      HarrisNumericalWeilLevel.classOf D C hΦ preservation composition unitCoherence
        associativity comparison symmetry stability square universality
        (D.harrisTaylorReflexStructure C q) compatibility h a.hom a.finiteFibers htor huT
        addT L q
        (levelDataBaseChange D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability b compatibility h a.hom a.finiteFibers (a.comp b).finiteFibers
          htor huS huT dualData U x) hx' hn' := by
  subst hp
  exact ⟨levelDataBaseChange_objectCondition D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b compatibility h a.hom a.finiteFibers (a.comp b).finiteFibers htor
    huS huT dualData p lieS x hx,
    HarrisNumericalWeilLevel.levelDataBaseChange_numericalObjectCondition D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability b compatibility h a.hom a.finiteFibers
    (a.comp b).finiteFibers htor huS huT dualData lieS L p x hn, rfl⟩

end PointPullback

local notation "DisBases" => ComponentwiseAdmissibleCMBaseCategory D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality

local notation "moduli" => smallLevelClassPresheafTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

local notation "presheaf" => disconnectedClassTowerPresheaf D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

local notation "component" => componentCMBase D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality

local notation "componentHom" => componentCMBaseHomTo D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality

local notation "pull" => unpointedClassTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

local notation "evaluate" => unpointedClassTowerEvaluationIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor

/-! ### The universal class at one represented level -/

section Universal
variable {U : SmallCMLevel D}
  (rep : CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor U)

/-- The universal class: the image of the lifted identity of the representing object
under the given representing isomorphism. -/
def cmUniversalClass : ((moduli).obj U).obj (op rep.base) :=
  uliftYonedaEquiv.{1} rep.represents.hom

local notation "universal" => cmUniversalClass D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor rep

/-- The universal class is the value of the representing map at the lifted identity. -/
theorem cmUniversalClass_eq :
    universal = rep.represents.hom.app (op rep.base) (ULift.up (𝟙 rep.base)) := rfl

/-- A map into the represented level recovers the pullback of its universal class. -/
theorem cmUniversalClass_pullback {S : DisBases} (a : S ⟶ rep.base) :
    ((moduli).obj U).map a.op universal =
      rep.represents.hom.app (op S) (ULift.up a) := by
  simpa [cmUniversalClass, uliftYonedaEquiv_comp] using
    (uliftYonedaEquiv_naturality.{1} (X := op rep.base) (Y := op S)
      rep.represents.hom a.op)

/-- The same pullback law, written with the existing disconnected tower presheaf. -/
theorem cmUniversalClass_pullback_presheaf {S : DisBases} (a : S ⟶ rep.base) :
    ((presheaf).map a.op).app U.obj universal =
      rep.represents.hom.app (op S) (ULift.up a) :=
  cmUniversalClass_pullback D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor rep a

/-- On a component `c` of the source, the pulled-back universal class is the pullback of
the universal class on any specified image component `d`, along the actual restricted
map of components. -/
theorem cmUniversalClass_pullback_component {S : DisBases} (a : S ⟶ rep.base)
    (c : _root_.ConnectedComponents S.obj.left)
    (d : _root_.ConnectedComponents rep.base.obj.left)
    (e : componentMap a.hom.left c = d) :
    (rep.represents.hom.app (op S) (ULift.up a)) c =
      (pull (componentHom a c d e)).app U.obj (universal d) := by
  rw [← cmUniversalClass_pullback]
  exact disconnectedClassTowerPullback_app_eq D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor a U.obj universal c d e

/-- The universal class evaluated on one actual component at a geometric point: a class
in the existing pointed normalized CM tower. -/
def cmUniversalComponentClass (c : _root_.ConnectedComponents rep.base.obj.left)
    (a : HarrisGeometricPoint (component rep.base c).obj.left) :=
  (evaluate (component rep.base c) a).hom.app U.obj (universal c)

local notation "pointedClass" => cmUniversalComponentClass D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor rep

/-- The class condition of the pointed class supplies an actual representative with its
determinant and numerical conditions; one is selected. -/
def cmUniversalComponentModel (c : _root_.ConnectedComponents rep.base.obj.left)
    (a : HarrisGeometricPoint (component rep.base c).obj.left) :=
  Classical.indefiniteDescription _ (pointedClass c a).property

/-- The selected actual representative over a component at a geometric point: a positive
polarized abelian scheme with its action and its level structure. -/
def cmUniversalComponentRepresentative (c : _root_.ConnectedComponents rep.base.obj.left)
    (a : HarrisGeometricPoint (component rep.base c).obj.left) :
    HarrisLevelData D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h a.hom a.finiteFibers htor
      (component rep.base c).property.torsionUnits U.obj :=
  (cmUniversalComponentModel D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor rep c a).1

local notation "representative" => cmUniversalComponentRepresentative D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor rep

/-- The representative satisfies the normalized determinant condition. -/
theorem cmUniversalComponentRepresentative_good
    (c : _root_.ConnectedComponents rep.base.obj.left)
    (a : HarrisGeometricPoint (component rep.base c).obj.left) :
    PositiveObjectCondition D C hΦ preservation composition unitCoherence associativity
      comparison symmetry stability square universality
      (D.harrisTaylorReflexStructure C (component rep.base c).obj.hom)
      (representative c a).1 :=
  (cmUniversalComponentModel D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor rep c a).2.fst

/-- The representative satisfies the dimension and central trace conditions. -/
theorem cmUniversalComponentRepresentative_numerical
    (c : _root_.ConnectedComponents rep.base.obj.left)
    (a : HarrisGeometricPoint (component rep.base c).obj.left) :
    HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality L
      (component rep.base c).obj.hom (representative c a).1 :=
  (cmUniversalComponentModel D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor rep c a).2.snd.2

local notation "good" => cmUniversalComponentRepresentative_good D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor rep
local notation "numerical" => cmUniversalComponentRepresentative_numerical D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor rep

/-- The class of the selected representative is the pointed universal class. -/
theorem cmUniversalComponentRepresentative_classOf
    (c : _root_.ConnectedComponents rep.base.obj.left)
    (a : HarrisGeometricPoint (component rep.base c).obj.left) :
    HarrisNumericalWeilLevel.classOf D C hΦ preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      (D.harrisTaylorReflexStructure C (component rep.base c).obj.hom) compatibility h
      a.hom a.finiteFibers htor (component rep.base c).property.torsionUnits
      (component rep.base c).property.pairAdditivity L (component rep.base c).obj.hom
      (representative c a) (good c a) (numerical c a) = pointedClass c a :=
  Subtype.ext (cmUniversalComponentModel D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor rep c a).2.snd.1

/-- An actual satisfying representative has the pointed universal class exactly when it
is related to the selected representative by the given relation: a rational polarized
isogeny carrying the level structure of the selected representative to its own. -/
theorem cmUniversalComponentRepresentative_classOf_iff
    (c : _root_.ConnectedComponents rep.base.obj.left)
    (a : HarrisGeometricPoint (component rep.base c).obj.left)
    (y : HarrisLevelData D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h a.hom a.finiteFibers htor
      (component rep.base c).property.torsionUnits U.obj)
    (hy : PositiveObjectCondition D C hΦ preservation composition unitCoherence associativity
      comparison symmetry stability square universality
      (D.harrisTaylorReflexStructure C (component rep.base c).obj.hom) y.1)
    (hny : HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality L
      (component rep.base c).obj.hom y.1) :
    letI := auxiliaryStarRing D C
    HarrisNumericalWeilLevel.classOf D C hΦ preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      (D.harrisTaylorReflexStructure C (component rep.base c).obj.hom) compatibility h
      a.hom a.finiteFibers htor (component rep.base c).property.torsionUnits
      (component rep.base c).property.pairAdditivity L (component rep.base c).obj.hom
      y hy hny = pointedClass c a ↔
    ∃ q : ℚˣ, ∃ e : (representative c a).1.actionObj ≅ y.1.actionObj,
      ∃ he : PolarizedWeilLevel.Multiple preservation composition unitCoherence
        associativity comparison symmetry stability square universality
        (component rep.base c).property.pairAdditivity (representative c a).1 y.1 q e,
      PolarizedWeilLevel.levelIso preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h
        A (D.harrisHodgePELForm C) a.hom a.finiteFibers htor
        (component rep.base c).property.torsionUnits
        (component rep.base c).property.pairAdditivity (representative c a).1 y.1
        ((hodgeLevelFunctor D C).obj U.obj) q e he (representative c a).2 = y.2 := by
  rw [← cmUniversalComponentRepresentative_classOf, eq_comm]
  exact HarrisNumericalWeilLevel.classOf_eq_iff D C hΦ preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    (D.harrisTaylorReflexStructure C (component rep.base c).obj.hom) compatibility h
    a.hom a.finiteFibers htor (component rep.base c).property.torsionUnits
    (component rep.base c).property.pairAdditivity L (component rep.base c).obj.hom
    (representative c a) y (good c a) hy (numerical c a) hny

/-- The universal class on each component is recovered from the selected representative
at any geometric point, through the inverse of the existing evaluation isomorphism. -/
theorem cmUniversalClass_component_eq (c : _root_.ConnectedComponents rep.base.obj.left)
    (a : HarrisGeometricPoint (component rep.base c).obj.left) :
    universal c = (evaluate (component rep.base c) a).inv.app U.obj
      (HarrisNumericalWeilLevel.classOf D C hΦ preservation composition unitCoherence
        associativity comparison symmetry stability square universality
        (D.harrisTaylorReflexStructure C (component rep.base c).obj.hom) compatibility h
        a.hom a.finiteFibers htor (component rep.base c).property.torsionUnits
        (component rep.base c).property.pairAdditivity L (component rep.base c).obj.hom
        (representative c a) (good c a) (numerical c a)) := by
  rw [cmUniversalComponentRepresentative_classOf]
  exact (congrArg (fun t => t.app U.obj (universal c))
    (evaluate (component rep.base c) a).hom_inv_id).symm

/-- Every component has a chosen geometric point from a residue-field closure. -/
def cmUniversalComponentPoint (c : _root_.ConnectedComponents rep.base.obj.left) :
    HarrisGeometricPoint (component rep.base c).obj.left :=
  HarrisGeometricPoint.ofResidue _ (Classical.arbitrary _)

local notation "componentPoint" => cmUniversalComponentPoint D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor rep

/-- The representative chosen on each component, at its chosen geometric point. -/
abbrev cmUniversalRepresentative (c : _root_.ConnectedComponents rep.base.obj.left) :=
  representative c (componentPoint c)

/-- The abelian scheme underlying the chosen representative on each component. -/
def cmUniversalAbelianFamily (c : _root_.ConnectedComponents rep.base.obj.left) :
    Langlands.AbelianScheme (component rep.base c).obj.left := by
  letI := auxiliaryStarRing D C
  exact (representative c (componentPoint c)).1.actionObj.abelianScheme

/-- The underlying abelian scheme of the chosen representative is the family. -/
theorem cmUniversalAbelianFamily_eq (c : _root_.ConnectedComponents rep.base.obj.left) :
    letI := auxiliaryStarRing D C
    cmUniversalAbelianFamily D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor rep c =
      (representative c (componentPoint c)).1.actionObj.abelianScheme := rfl

/-- Pulling back the universal class along any actual map to the level, on each source
component, is the existing pullback of the class of the chosen representative over the
image component. -/
theorem cmUniversalClass_pullback_representative {S : DisBases} (f : S ⟶ rep.base)
    (c : _root_.ConnectedComponents S.obj.left)
    (d : _root_.ConnectedComponents rep.base.obj.left)
    (e : componentMap f.hom.left c = d) :
    (rep.represents.hom.app (op S) (ULift.up f)) c =
      (pull (componentHom f c d e)).app U.obj
        ((evaluate (component rep.base d) (componentPoint d)).inv.app U.obj
          (HarrisNumericalWeilLevel.classOf D C hΦ preservation composition unitCoherence
            associativity comparison symmetry stability square universality
            (D.harrisTaylorReflexStructure C (component rep.base d).obj.hom) compatibility h
            (componentPoint d).hom (componentPoint d).finiteFibers htor
            (component rep.base d).property.torsionUnits
            (component rep.base d).property.pairAdditivity L (component rep.base d).obj.hom
            (representative d (componentPoint d)) (good d (componentPoint d))
            (numerical d (componentPoint d)))) := by
  rw [cmUniversalClass_pullback_component D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor rep f c d e,
    ← cmUniversalClass_component_eq]

/-- At every geometric point `t` of a source component, the pulled-back universal class is
the class of the actual base change of the chosen representative over the image component,
after moving its level structure along any fibre-functor path to the image of `t`. -/
theorem cmUniversalClass_pullback_baseChange {S : DisBases} (f : S ⟶ rep.base)
    (c : _root_.ConnectedComponents S.obj.left)
    (d : _root_.ConnectedComponents rep.base.obj.left)
    (e : componentMap f.hom.left c = d)
    (t : HarrisGeometricPoint (component S c).obj.left)
    (path : fiberFunctor (componentPoint d).hom (componentPoint d).finiteFibers ≅
      fiberFunctor (t.comp (componentHom f c d e).hom.left).hom
        (t.comp (componentHom f c d e).hom.left).finiteFibers) :
    ∃ hx hn,
      (evaluate (component S c) t).hom.app U.obj
          ((rep.represents.hom.app (op S) (ULift.up f)) c) =
        HarrisNumericalWeilLevel.classOf D C hΦ preservation composition unitCoherence
          associativity comparison symmetry stability square universality
          (D.harrisTaylorReflexStructure C (component S c).obj.hom) compatibility h
          t.hom t.finiteFibers htor (component S c).property.torsionUnits
          (component S c).property.pairAdditivity L (component S c).obj.hom
          (levelDataBaseChange D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality dualityNaturality
            polarizationStability (componentHom f c d e).hom.left compatibility h t.hom
            t.finiteFibers (t.comp (componentHom f c d e).hom.left).finiteFibers htor
            (component rep.base d).property.torsionUnits
            (component S c).property.torsionUnits
            (unpointedPullbackDualData D C preservation composition unitCoherence associativity
              comparison symmetry stability square universality (componentHom f c d e))
            U.obj
            (HarrisTaylorLieWeilLevel.pointMapRepresentative D C preservation composition
              unitCoherence associativity comparison symmetry stability square universality
              compatibility h htor (component rep.base d).property.torsionUnits path U.obj
              (representative d (componentPoint d)))) hx hn := by
  let g := componentHom f c d e
  have hmove := classGeometricPointTowerIso_eq_path D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    (component rep.base d).obj.hom compatibility h htor
    (component rep.base d).property.torsionUnits
    (component rep.base d).property.pairAdditivity path
  obtain ⟨hx, hn, hpull⟩ := geometricFamilyPointPullback_classOf D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor g.hom.left
    (component rep.base d).obj.hom (component S c).obj.hom (Over.w g.hom)
    (component rep.base d).property.lieNaturality
    (component rep.base d).property.torsionUnits (component S c).property.torsionUnits
    (unpointedPullbackDualData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality g)
    (component rep.base d).property.pairAdditivity (component S c).property.pairAdditivity t
    (HarrisTaylorLieWeilLevel.pointMapRepresentative D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      compatibility h htor (component rep.base d).property.torsionUnits path U.obj
      (representative d (componentPoint d)))
    (good d (componentPoint d)) (numerical d (componentPoint d))
  refine ⟨hx, hn, ?_⟩
  rw [cmUniversalClass_pullback_representative D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor rep f c d e, ← hpull]
  exact congrArg (fun i => (geometricFamilyPointPullback D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor g.hom.left
      (component rep.base d).obj.hom (component S c).obj.hom (Over.w g.hom)
      (component rep.base d).property.lieNaturality
      (component rep.base d).property.torsionUnits (component S c).property.torsionUnits
      (unpointedPullbackDualData D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality g)
      (component rep.base d).property.pairAdditivity (component S c).property.pairAdditivity
      t).app U.obj
    (i.hom.app U.obj (HarrisNumericalWeilLevel.classOf D C hΦ preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      (D.harrisTaylorReflexStructure C (component rep.base d).obj.hom) compatibility h
      (componentPoint d).hom (componentPoint d).finiteFibers htor
      (component rep.base d).property.torsionUnits
      (component rep.base d).property.pairAdditivity L (component rep.base d).obj.hom
      (representative d (componentPoint d)) (good d (componentPoint d))
      (numerical d (componentPoint d))))) hmove

end Universal

/-! ### Compatibility along the represented level maps -/

section Levels
variable (R : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)

local notation "baseTower" => representedCMBaseTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

local notation "universalAt" => cmUniversalClass D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor

/-- Pulling back the universal class of the target level along the actual transition map
gives the image of the universal class of the source level under the moduli transition. -/
theorem cmUniversalClass_transition {U V : SmallCMLevel D} (k : U ⟶ V) :
    ((moduli).obj V).map ((baseTower R).map k).op (universalAt (R V)) =
      ((moduli).map k).app (op (R U).base) (universalAt (R U)) := by
  refine (cmUniversalClass_pullback D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor (R V) ((baseTower R).map k)).trans ?_
  have e := representedCMBaseTower_map_classes D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor R k ((baseTower R).obj U) (𝟙 _)
  refine Eq.trans ?_ e
  exact congrArg (fun g => (R V).represents.hom.app (op ((baseTower R).obj U)) (ULift.up g))
    (Category.id_comp ((baseTower R).map k)).symm

/-- The componentwise form: on a component `c` of the source level with image component
`d`, the pulled-back universal class of the target level is the image of the universal
class of the source level under the original level arrow. -/
theorem cmUniversalClass_transition_component {U V : SmallCMLevel D} (k : U ⟶ V)
    (c : _root_.ConnectedComponents (R U).base.obj.left)
    (d : _root_.ConnectedComponents (R V).base.obj.left)
    (e : componentMap ((baseTower R).map k).hom.left c = d) :
    (pull (componentHom ((baseTower R).map k) c d e)).app V.obj (universalAt (R V) d) =
      (unpointedClassTower D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h htor
        (component (R U).base c)).map ((ObjectProperty.ι _).map k) (universalAt (R U) c) := by
  have t := congrFun (cmUniversalClass_transition D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor R k) c
  exact (disconnectedClassTowerPullback_app_eq D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor ((baseTower R).map k) V.obj
    (universalAt (R V)) c d e).symm.trans t

/-- The representatives are compatible with the level maps up to the actual rational
isogeny class: at every geometric point of a component of the source level, the class of
the actual base change of the target-level representative equals the class of the
source-level representative with its level structure pushed along the level arrow. -/
theorem cmUniversalRepresentative_transition {U V : SmallCMLevel D} (k : U ⟶ V)
    (c : _root_.ConnectedComponents (R U).base.obj.left)
    (d : _root_.ConnectedComponents (R V).base.obj.left)
    (e : componentMap ((baseTower R).map k).hom.left c = d)
    (t : HarrisGeometricPoint (component (R U).base c).obj.left)
    (path : fiberFunctor (cmUniversalComponentPoint D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor (R V) d).hom
        (cmUniversalComponentPoint D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor (R V) d).finiteFibers ≅
      fiberFunctor (t.comp (componentHom ((baseTower R).map k) c d e).hom.left).hom
        (t.comp (componentHom ((baseTower R).map k) c d e).hom.left).finiteFibers) :
    ∃ hx hn,
      HarrisNumericalWeilLevel.classOf D C hΦ preservation composition unitCoherence
          associativity comparison symmetry stability square universality
          (D.harrisTaylorReflexStructure C (component (R U).base c).obj.hom) compatibility h
          t.hom t.finiteFibers htor (component (R U).base c).property.torsionUnits
          (component (R U).base c).property.pairAdditivity L
          (component (R U).base c).obj.hom
          (levelDataBaseChange D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality dualityNaturality
            polarizationStability (componentHom ((baseTower R).map k) c d e).hom.left
            compatibility h t.hom t.finiteFibers
            (t.comp (componentHom ((baseTower R).map k) c d e).hom.left).finiteFibers htor
            (component (R V).base d).property.torsionUnits
            (component (R U).base c).property.torsionUnits
            (unpointedPullbackDualData D C preservation composition unitCoherence associativity
              comparison symmetry stability square universality
              (componentHom ((baseTower R).map k) c d e))
            V.obj
            (HarrisTaylorLieWeilLevel.pointMapRepresentative D C preservation composition
              unitCoherence associativity comparison symmetry stability square universality
              compatibility h htor (component (R V).base d).property.torsionUnits path V.obj
              (cmUniversalComponentRepresentative D C preservation composition unitCoherence
                associativity comparison symmetry stability square universality
                dualityNaturality polarizationStability compatibility h htor (R V) d
                (cmUniversalComponentPoint D C preservation composition unitCoherence
                  associativity comparison symmetry stability square universality
                  dualityNaturality polarizationStability compatibility h htor (R V) d))))
          hx hn =
        HarrisNumericalWeilLevel.classOf D C hΦ preservation composition unitCoherence
          associativity comparison symmetry stability square universality
          (D.harrisTaylorReflexStructure C (component (R U).base c).obj.hom) compatibility h
          t.hom t.finiteFibers htor (component (R U).base c).property.torsionUnits
          (component (R U).base c).property.pairAdditivity L
          (component (R U).base c).obj.hom
          (HarrisNumericalWeilLevel.mapRepresentative D C preservation composition
            unitCoherence associativity comparison symmetry stability square universality
            compatibility h t.hom t.finiteFibers htor
            (component (R U).base c).property.torsionUnits ((ObjectProperty.ι _).map k)
            (cmUniversalComponentRepresentative D C preservation composition unitCoherence
              associativity comparison symmetry stability square universality
              dualityNaturality polarizationStability compatibility h htor (R U) c t))
          (cmUniversalComponentRepresentative_good D C preservation composition unitCoherence
            associativity comparison symmetry stability square universality
            dualityNaturality polarizationStability compatibility h htor (R U) c t)
          (cmUniversalComponentRepresentative_numerical D C preservation composition
            unitCoherence associativity comparison symmetry stability square universality
            dualityNaturality polarizationStability compatibility h htor (R U) c t) := by
  obtain ⟨hx, hn, hbase⟩ := cmUniversalClass_pullback_baseChange D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor (R V)
    ((baseTower R).map k) c d e t path
  have hc := cmUniversalComponentRepresentative_classOf D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor (R U) c t
  refine ⟨hx, hn, hbase.symm.trans ?_⟩
  refine (congrArg (fun z => (evaluate (component (R U).base c) t).hom.app V.obj z)
    ((cmUniversalClass_pullback_component D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor (R V) ((baseTower R).map k) c d e).trans
      (cmUniversalClass_transition_component D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor R k c d e))).trans ?_
  exact (congrArg (fun z => (geometricClassTower D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality
    (component (R U).base c).obj.hom compatibility h htor
    (component (R U).base c).property.torsionUnits
    (component (R U).base c).property.pairAdditivity t).map ((ObjectProperty.ι _).map k) z)
    hc).symm

end Levels

/-! ### The chosen representations and the scheme tower -/

section Chosen
variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

local notation "chosen" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

/-- The level of the actual scheme tower is the representing scheme of the chosen
representation. -/
theorem cmSchemeTower_obj (U : SmallCMLevel D) :
    (cmSchemeTower D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q).obj U = (chosen U).base.obj.left := rfl

/-- The transition of the actual scheme tower is the underlying scheme map of the
represented transition. -/
theorem cmSchemeTower_map {U V : SmallCMLevel D} (k : U ⟶ V) :
    (cmSchemeTower D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q).map k =
      ((representedCMBaseTower D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor chosen).map k).hom.left := rfl

/-- The universal class at a small level of the scheme tower. -/
abbrev cmSchemeTowerUniversalClass (U : SmallCMLevel D) :=
  cmUniversalClass D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor (chosen U)

/-- The abelian family over the components of a level of the scheme tower. -/
abbrev cmSchemeTowerAbelianFamily (U : SmallCMLevel D) :=
  cmUniversalAbelianFamily D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor (chosen U)

end Chosen

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
