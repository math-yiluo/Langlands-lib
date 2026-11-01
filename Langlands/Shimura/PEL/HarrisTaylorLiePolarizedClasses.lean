import Langlands.Shimura.PEL.HarrisPolarizedWeilTower
import Langlands.Shimura.PEL.HarrisTaylorLieClasses

/-! # Positive Lie compatibility on actual Harris polarized level classes -/

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

local notation "PositiveObject" => PositivePolarizedAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality (S := S)

/-- The actual positive Lie tensor rank and central scalar equality on a polarized object. -/
def LieObjectCondition (X : PositiveObject) : Prop :=
  letI := auxiliaryStarRing D C
  HarrisTaylor.LieCompatibility L E p X.actionObj.abelianScheme X.actionObj.action n

local notation "LieGood" => LieObjectCondition D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p

/-- The same positive polarized object has the prescribed dimension and positive Lie condition. -/
def ObjectCondition (X : PositiveObject) : Prop :=
  letI := auxiliaryStarRing D C
  HarrisTaylor.DimensionLieCondition L E p n X.actionObj.abelianScheme X.actionObj.action

local notation "Good" => ObjectCondition D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p

/-- The geometric dimension and positive Lie condition refer to the identical abelian scheme. -/
theorem objectCondition_iff (X : PositiveObject) :
    Good X ↔
      (letI := auxiliaryStarRing D C
       HarrisTaylor.PrescribedRelativeDimension E X.actionObj.abelianScheme n) ∧ LieGood X :=
  Iff.rfl

variable
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [QuasiSeparatedSpace S]
  (additivity : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))

local notation "Level" => HarrisLevel D
local notation "Data" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu

/-- The existing actual positive polarized quotient at the transported original Harris level. -/
abbrev AmbientClass (U : Level) :=
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.IsoClass preservation composition unitCoherence associativity
    comparison symmetry stability square universality compatibility h
    A (D.harrisHodgePELForm C) s hs htor hu additivity ((hodgeLevelFunctor D C).obj U)

local notation "Ambient" => AmbientClass D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu additivity

/-- Form the actual polarized-isogeny class, retaining its compatible fixed level orbit. -/
def ambientClassOf {U : Level} (x : Data U) : Ambient U :=
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.classOf preservation composition unitCoherence associativity
    comparison symmetry stability square universality compatibility h
    A (D.harrisHodgePELForm C) s hs htor hu additivity x

local notation "ambientMk" => ambientClassOf D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu additivity

/-- Forget actual polarization and levels into the actual equivariant rational action quotient. -/
def forgetAction {U : Level} (q : Ambient U) : RationalAlgebraAction.IsoClass S A :=
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.forgetAction preservation composition unitCoherence associativity
    comparison symmetry stability square universality compatibility h
    A (D.harrisHodgePELForm C) s hs htor hu additivity q

local notation "forget" => forgetAction D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu additivity

@[simp] theorem forgetAction_ambientClassOf {U : Level} (x : Data U) :
    letI := auxiliaryStarRing D C
    forget (ambientMk x) = RationalAlgebraAction.classOf x.1.actionObj := rfl

/-- Positive Lie compatibility is an invariant predicate on the actual polarized quotient. -/
def LieClassCondition {U : Level} (q : Ambient U) : Prop :=
  HarrisTaylor.LieCompatibilityClassCondition L E p n (forget q)

local notation "LieCondition" => LieClassCondition D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
  compatibility h s hs htor hu additivity

@[simp] theorem lieClassCondition_ambientClassOf {U : Level} (x : Data U) :
    LieCondition (ambientMk x) ↔ LieGood x.1 := Iff.rfl

/-- The positive Lie predicate agrees with every representative of the polarized class. -/
theorem lieClassCondition_iff_of_ambientClassOf_eq {U : Level}
    (q : Ambient U) (x : Data U) (hx : ambientMk x = q) :
    LieCondition q ↔ LieGood x.1 := by
  subst q
  rfl

/-- One actual polarized representative with its actual level orbit satisfies both conditions. -/
def ClassCondition {U : Level} (q : Ambient U) : Prop :=
  ∃ x : Data U, ambientMk x = q ∧ Good x.1

local notation "Condition" => ClassCondition D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
  compatibility h s hs htor hu additivity

/-- Invariance transfers the Lie condition to the same representative witnessing dimension. -/
theorem classCondition_iff {U : Level} (q : Ambient U) :
    Condition q ↔ LieCondition q ∧
      ∃ x : Data U, ambientMk x = q ∧
        (letI := auxiliaryStarRing D C
         HarrisTaylor.PrescribedRelativeDimension E x.1.actionObj.abelianScheme n) := by
  constructor
  · rintro ⟨x, hx, hdim, hlie⟩
    exact ⟨(lieClassCondition_iff_of_ambientClassOf_eq D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality L p
      compatibility h s hs htor hu additivity q x hx).mpr hlie, x, hx, hdim⟩
  · rintro ⟨hlie, x, hx, hdim⟩
    exact ⟨x, hx, hdim, (lieClassCondition_iff_of_ambientClassOf_eq D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality L p compatibility h s hs htor hu additivity q x hx).mp hlie⟩

/-- Every actual representative of the joint image satisfies positive Lie compatibility. -/
theorem classCondition_lie {U : Level} (q : Ambient U) (hq : Condition q)
    (x : Data U) (hx : ambientMk x = q) : LieGood x.1 :=
  (lieClassCondition_iff_of_ambientClassOf_eq D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality L p
    compatibility h s hs htor hu additivity q x hx).mp
    ((classCondition_iff D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality L p compatibility h s hs htor hu additivity q).mp hq).1

/-- The actual polarized dimension-and-Lie representative image at an original Harris level. -/
def IsoClass (U : Level) := {q : Ambient U // Condition q}

local notation "Classes" => IsoClass D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
  compatibility h s hs htor hu additivity

/-- Form the class of an actual jointly satisfying polarized level representative. -/
def classOf {U : Level} (x : Data U) (hx : Good x.1) : Classes U :=
  ⟨ambientMk x, x, rfl, hx⟩

local notation "mkClass" => classOf D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
  compatibility h s hs htor hu additivity

@[simp] theorem classOf_val {U : Level} (x : Data U) (hx : Good x.1) :
    (mkClass x hx).val = ambientMk x := rfl

/-- Every image class has one actual representative satisfying both conditions. -/
theorem classOf_surjective {U : Level} (q : Classes U) :
    ∃ (x : Data U) (hx : Good x.1), mkClass x hx = q := by
  obtain ⟨x, hx, h⟩ := q.property
  exact ⟨x, h, Subtype.ext hx⟩

/-- Equality retains the actual rational inverse, geometric multiplier and compatible-orbit equation. -/
theorem classOf_eq_iff {U : Level} (x y : Data U) (hx : Good x.1) (hy : Good y.1) :
    letI := auxiliaryStarRing D C
    mkClass x hx = mkClass y hy ↔
      ∃ q : ℚˣ, ∃ e : x.1.actionObj ≅ y.1.actionObj,
        ∃ he : PolarizedWeilLevel.Multiple preservation composition unitCoherence
          associativity comparison symmetry stability square universality additivity x.1 y.1 q e,
        PolarizedWeilLevel.levelIso preservation composition unitCoherence associativity
          comparison symmetry stability square universality compatibility h
          A (D.harrisHodgePELForm C) s hs htor hu additivity x.1 y.1
          ((hodgeLevelFunctor D C).obj U) q e he x.2 = y.2 := by
  let := auxiliaryStarRing D C
  rw [Subtype.ext_iff]
  exact PolarizedWeilLevel.classOf_eq_iff preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h
    A (D.harrisHodgePELForm C) s hs htor hu additivity

/-- Forgetting the conditions embeds the image in the existing actual polarized quotient. -/
theorem val_injective {U : Level} :
    Function.Injective (fun q : Classes U => q.val) := Subtype.val_injective

/-- Forget polarization and levels using the very same dimension-and-Lie representative. -/
def forgetDimensionLieAction {U : Level} (q : Classes U) :
    HarrisTaylor.DimensionLieActionClass L E p n (A := A) := by
  letI := auxiliaryStarRing D C
  refine ⟨forget q.val, ?_⟩
  obtain ⟨x, hx, hgood⟩ := q.property
  exact ⟨x.1.actionObj, by rw [← hx]; rfl, hgood⟩

local notation "forgetJoint" => forgetDimensionLieAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality L p
  compatibility h s hs htor hu additivity

@[simp] theorem forgetDimensionLieAction_val {U : Level} (q : Classes U) :
    (forgetJoint q).val = forget q.val := rfl

@[simp] theorem forgetDimensionLieAction_classOf {U : Level} (x : Data U) (hx : Good x.1) :
    letI := auxiliaryStarRing D C
    forgetJoint (mkClass x hx) = HarrisTaylor.dimensionLieActionClassOf L E p n x.1.actionObj hx :=
  rfl

/-- Every action representative of the forgotten class has actual positive Lie compatibility. -/
theorem forgetDimensionLieAction_lie {U : Level} (q : Classes U)
    (X : RationalAlgebraAction S A)
    (hX : RationalAlgebraAction.classOf X = (forgetJoint q).val) :
    HarrisTaylor.LieCompatibility L E p X.abelianScheme X.action n :=
  HarrisTaylor.dimensionLieActionClassCondition_lieCompatibility L E p n
    (forgetJoint q).val (forgetJoint q).property X hX

end Langlands.Shimura.PEL.HarrisTaylorLieWeilLevel
