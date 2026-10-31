import Langlands.Shimura.PEL.HarrisPolarizedWeilTower
import Langlands.Shimura.PEL.HarrisTaylorNumericalClasses

/-! # Numerical representative images in the original Harris polarized tower -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisNumericalWeilLevel

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
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (hΦ : IsCMSection E F Φ)
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
  (b : S ⟶ Spec (.of (D.kottwitzCocharacterReflexField C)))
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
  (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L F]
  (p : S ⟶ Spec (.of F))

local notation "Level" => HarrisLevel D
local notation "OriginalGroup" =>
  D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ
local notation "indexFunctor" => hodgeLevelFunctor D C
local notation "Data" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu
local notation "Good" => PositiveObjectCondition D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality b
local notation "ambientTower" => harrisIsoClassTower D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality b
  compatibility h s hs htor hu additivity
local notation "Ambient" => HarrisIsoClass D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  s hs htor hu additivity
local notation "ambientMk" => harrisClassOf D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  s hs htor hu additivity

/-- The exact geometric dimension and central trace tests on an actual positive object. -/
def NumericalObjectCondition
    (X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := S)) : Prop :=
  letI := auxiliaryStarRing D C
  HarrisTaylor.NumericalCondition L p E X.actionObj.abelianScheme X.actionObj.action n

local notation "Num" => NumericalObjectCondition D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p

/-- The actual image of determinant-compatible, numerically satisfying representatives. -/
def ClassCondition {U : Level} (q : Ambient U) : Prop :=
  ∃ (x : Data U) (hx : Good x.1), ambientMk x hx = q ∧ Num x.1

local notation "Condition" => ClassCondition D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  s hs htor hu additivity L p

/-- Classes with a single actual representative carrying all the displayed conditions. -/
def IsoClass (U : Level) := {q : Ambient U // Condition q}

local notation "Classes" => IsoClass D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  s hs htor hu additivity L p

/-- Form the image class of an actual representative satisfying both tests. -/
def classOf {U : Level} (x : Data U) (hx : Good x.1) (hn : Num x.1) : Classes U :=
  ⟨ambientMk x hx, x, hx, rfl, hn⟩

local notation "mkClass" => classOf D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  s hs htor hu additivity L p

@[simp] theorem classOf_val {U : Level}
    (x : Data U) (hx : Good x.1) (hn : Num x.1) :
    (mkClass x hx hn).val = ambientMk x hx := rfl

/-- Every image class has an actual representative satisfying all the conditions. -/
theorem classOf_surjective {U : Level} (q : Classes U) :
    ∃ (x : Data U) (hx : Good x.1) (hn : Num x.1), mkClass x hx hn = q := by
  obtain ⟨x, hx, hq, hn⟩ := q.property
  exact ⟨x, hx, hn, Subtype.ext hq⟩

/-- Equality retains exactly the actual polarized-isogeny and compatible-orbit relation. -/
theorem classOf_eq_iff {U : Level} (x y : Data U)
    (hx : Good x.1) (hy : Good y.1) (hnx : Num x.1) (hny : Num y.1) :
    letI := auxiliaryStarRing D C
    mkClass x hx hnx = mkClass y hy hny ↔
      ∃ q : ℚˣ, ∃ e : x.1.actionObj ≅ y.1.actionObj,
        ∃ he : PolarizedWeilLevel.Multiple preservation composition unitCoherence
          associativity comparison symmetry stability square universality additivity x.1 y.1 q e,
        PolarizedWeilLevel.levelIso preservation composition unitCoherence associativity
          comparison symmetry stability square universality compatibility h
          A (D.harrisHodgePELForm C) s hs htor hu additivity x.1 y.1
          ((indexFunctor).obj U) q e he x.2 = y.2 := by
  let := auxiliaryStarRing D C
  rw [Subtype.ext_iff]
  exact harrisClassOf_eq_iff D C hΦ preservation composition unitCoherence associativity
    comparison symmetry stability square universality b compatibility h
    s hs htor hu additivity x y hx hy

/-- The actual original-group transporter retains the same geometric object. -/
def mapRepresentative {U V : Level} (f : U ⟶ V) (x : Data U) : Data V := by
  letI := auxiliaryStarRing D C
  exact PolarizedWeilLevel.mapData preservation composition unitCoherence associativity
    comparison symmetry stability square universality compatibility h
    A (D.harrisHodgePELForm C) s hs htor hu ((indexFunctor).map f) x

local notation "mapRep" => mapRepresentative D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu

/-- Preservation of the numerical image uses its actual satisfying representative. -/
theorem classCondition_map {U V : Level} (f : U ⟶ V) (q : Ambient U)
    (hq : Condition q) : Condition ((ambientTower).map f q) := by
  obtain ⟨x, hx, hq, hn⟩ := hq
  refine ⟨mapRep f x, hx, ?_, hn⟩
  rw [← hq]
  rfl

/-- Actual transporter maps restrict to the numerical representative image. -/
def classMap {U V : Level} (f : U ⟶ V) (q : Classes U) : Classes V :=
  ⟨(ambientTower).map f q.val,
    classCondition_map D C hΦ preservation composition unitCoherence associativity
      comparison symmetry stability square universality b compatibility h
      s hs htor hu additivity L p f q.val q.property⟩

local notation "mapClass" => classMap D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  s hs htor hu additivity L p

@[simp] theorem classMap_val {U V : Level} (f : U ⟶ V) (q : Classes U) :
    (mapClass f q).val = (ambientTower).map f q.val := rfl

@[simp] theorem classMap_classOf {U V : Level} (f : U ⟶ V)
    (x : Data U) (hx : Good x.1) (hn : Num x.1) :
    mapClass f (mkClass x hx hn) = mkClass (mapRep f x) hx hn := rfl

/-- A genuine tower of classes of actual numerical polarized representatives. -/
def isoClassTower : Level ⥤ Type 1 where
  obj U := Classes U
  map f := ↾(mapClass f)
  map_id U := by
    ext q
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((ambientTower).map_id U) q.val
  map_comp f g := by
    ext q
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((ambientTower).map_comp f g) q.val

local notation "tower" => isoClassTower D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  s hs htor hu additivity L p

/-- Natural inclusion into the original actual positive polarized determinant tower. -/
def inclusionNatTrans : tower ⟶ ambientTower where
  app _ := ↾Subtype.val
  naturality {_U _V} _f := rfl

/-- The numerical image embeds in the actual ambient polarized determinant classes. -/
theorem val_injective {U : Level} :
    Function.Injective (fun q : Classes U => q.val) := Subtype.val_injective

/-- Forget polarization and levels into the constructed numerical action-class image. -/
def forgetNumericalAction {U : Level} (q : Classes U) :
    HarrisTaylor.NumericalActionClass L F p n E (A := A) := by
  letI := auxiliaryStarRing D C
  exact ⟨((harrisForgetDeterminantActionNatTrans D C hΦ preservation composition unitCoherence
    associativity comparison symmetry stability square universality b compatibility h
    s hs htor hu additivity).app U q.val).val, by
      obtain ⟨x, hx, hq, hn⟩ := q.property
      refine ⟨x.1.actionObj, ?_, hn⟩
      rw [← hq]
      rfl⟩

local notation "forgetNum" => forgetNumericalAction D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality b
  compatibility h s hs htor hu additivity L p

@[simp] theorem forgetNumericalAction_classOf {U : Level}
    (x : Data U) (hx : Good x.1) (hn : Num x.1) :
    letI := auxiliaryStarRing D C
    forgetNum (mkClass x hx hn) =
      HarrisTaylor.numericalActionClassOf L F p n E x.1.actionObj hn := rfl

/-- The numerical action class is unchanged along all original level arrows. -/
theorem forgetNumericalAction_classMap {U V : Level} (f : U ⟶ V) (q : Classes U) :
    forgetNum (mapClass f q) = forgetNum q := by
  obtain ⟨x, hx, hn, hq⟩ := classOf_surjective D C hΦ preservation composition
    unitCoherence associativity comparison symmetry stability square universality b
    compatibility h s hs htor hu additivity L p q
  rw [← hq]
  rfl

/-- Forgetting to numerical action classes is a natural transformation. -/
def forgetNumericalActionNatTrans :
    tower ⟶ (Functor.const Level).obj
      (HarrisTaylor.NumericalActionClass L F p n E (A := A)) where
  app _ := ↾forgetNum
  naturality {U V} f := by
    ext q
    exact forgetNumericalAction_classMap D C hΦ preservation composition unitCoherence
      associativity comparison symmetry stability square universality b compatibility h
      s hs htor hu additivity L p f q

/-- Forget an original subgroup through its actual inclusion arrow. -/
def forgetLevel {U V : Level} (hU : U.subgroup ≤ V.subgroup) :
    Classes U → Classes V :=
  mapClass (CompactOpenLevel.inclusion hU)

include D C in
omit [IsCMField F] [IsScalarTower ℚ F A] in
private theorem rationalFinite : Module.Finite ℚ A :=
  (hodgeRationalPELConditions D C).finite_module

/-- The inclusion leg from the actual original-Harris Hecke intersection. -/
def heckeLeft (U V : Level) (g : OriginalGroup) :
    letI := rationalFinite D C
    Classes (CompactOpenLevel.heckeLevel U V g) → Classes U := by
  letI := rationalFinite D C
  exact fun q => mapClass (CompactOpenLevel.heckeLeft U V g) q

/-- The right-translation leg from the same original-Harris Hecke intersection. -/
def heckeRight (U V : Level) (g : OriginalGroup) :
    letI := rationalFinite D C
    Classes (CompactOpenLevel.heckeLevel U V g) → Classes V := by
  letI := rationalFinite D C
  exact fun q => mapClass (CompactOpenLevel.heckeRight U V g) q

@[simp] theorem heckeLeft_classOf (U V : Level) (g : OriginalGroup)
    (x : letI := rationalFinite D C
      Data (CompactOpenLevel.heckeLevel U V g))
    (hx : Good x.1) (hn : Num x.1) :
    letI := rationalFinite D C
    heckeLeft D C hΦ preservation composition unitCoherence associativity
      comparison symmetry stability square universality b compatibility h
      s hs htor hu additivity L p U V g (mkClass x hx hn) =
      mkClass (mapRep (CompactOpenLevel.heckeLeft U V g) x) hx hn := rfl

@[simp] theorem heckeRight_classOf (U V : Level) (g : OriginalGroup)
    (x : letI := rationalFinite D C
      Data (CompactOpenLevel.heckeLevel U V g))
    (hx : Good x.1) (hn : Num x.1) :
    letI := rationalFinite D C
    heckeRight D C hΦ preservation composition unitCoherence associativity
      comparison symmetry stability square universality b compatibility h
      s hs htor hu additivity L p U V g (mkClass x hx hn) =
      mkClass (mapRep (CompactOpenLevel.heckeRight U V g) x) hx hn := rfl

end Langlands.Shimura.PEL.HarrisNumericalWeilLevel
