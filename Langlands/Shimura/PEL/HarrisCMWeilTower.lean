import Langlands.Shimura.PEL.HarrisNumericalWeilTower
import Langlands.Shimura.PEL.HarrisTaylorCMLieDeterminant

/-! # The actual Harris numerical Weil tower with normalized CM coefficients -/

noncomputable section

open CategoryTheory _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

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

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "b" => D.harrisTaylorReflexStructure C p
local notation "Level" => HarrisLevel D
local notation "OriginalGroup" =>
  D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ
local notation "PositiveObject" => PositivePolarizedAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality (S := S)
local notation "Good" => PositiveObjectCondition D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality b
local notation "Num" => HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality L p

/-- The normalized determinant and numerical tests on the same actual action through `p`. -/
def ObjectCondition (X : PositiveObject) : Prop :=
  letI := auxiliaryStarRing D C
  D.HarrisTaylorCMRationalLieDeterminantCondition C p X.actionObj.abelianScheme X.actionObj.action ∧
    HarrisTaylor.NumericalCondition L p E X.actionObj.abelianScheme X.actionObj.action n

local notation "Condition" => ObjectCondition D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p

/-- The reflex base uses the explicit normalized map from the same CM structure map. -/
theorem objectCondition_iff (X : PositiveObject) :
    Condition X ↔ Good X ∧ Num X := by
  let := auxiliaryStarRing D C
  exact and_congr
    (D.harrisTaylorCMRationalLieDeterminantCondition_iff C p
      X.actionObj.abelianScheme X.actionObj.action) Iff.rfl

/-- The object condition forces the prescribed arithmetic coefficient of the actual
binary Lie polynomial for every central element in the actual order. -/
theorem objectCondition_centralCoefficient (X : PositiveObject) (hx : Condition X) :
    letI := auxiliaryStarRing D C
    ∀ {U : S.Opens} {I : Type} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅
      X.actionObj.abelianScheme.Lie.over U)
    (a : F) (c : D.harrisHodgePELIntegralOrder C)
    (_hc : (c : A) = algebraMap F A a) (V : Over U),
    HodgeDeterminant.traceCoefficient
      (lieRationalSectionDeterminant p X.actionObj.abelianScheme
        (D.harrisRationalOrderAction C X.actionObj.abelianScheme X.actionObj.action)
        e ![1, c] V) = HarrisTaylor.lieTraceSection L p n a V.left := by
  let := auxiliaryStarRing D C
  intro U I _ e a c hc V
  exact D.harrisTaylorCMRationalLieDeterminantConditionAt_centralCoefficient C p
    X.actionObj.abelianScheme X.actionObj.action e a c hc V
    (hx.1 (Fin 2) ![1, c] U I e V)

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

local notation "Data" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu
local notation "oldMk" => HarrisNumericalWeilLevel.classOf D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality b
  compatibility h s hs htor hu additivity L p

/-- The numerical representative image at the actual CM-induced reflex structure. -/
abbrev IsoClass (U : Level) :=
  HarrisNumericalWeilLevel.IsoClass D C hΦ preservation composition unitCoherence
    associativity comparison symmetry stability square universality b compatibility h
    s hs htor hu additivity L p U

local notation "Classes" => IsoClass D C preservation composition unitCoherence associativity
  comparison symmetry stability square universality p compatibility h s hs htor hu additivity

/-- The class of an actual representative satisfying the single-map conjunction. -/
def classOf {U : Level} (x : Data U) (hx : Condition x.1) : Classes U :=
  oldMk x ((objectCondition_iff D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality p x.1).mp hx).1
    ((objectCondition_iff D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p x.1).mp hx).2

local notation "mkClass" => classOf D C preservation composition unitCoherence associativity
  comparison symmetry stability square universality p compatibility h s hs htor hu additivity

/-- Every class has one actual representative satisfying both tests through `p`. -/
theorem classOf_surjective {U : Level} (q : Classes U) :
    ∃ (x : Data U) (hx : Condition x.1), mkClass x hx = q := by
  obtain ⟨x, hx, hn, hq⟩ := HarrisNumericalWeilLevel.classOf_surjective D C hΦ
    preservation composition unitCoherence associativity comparison symmetry stability
    square universality b compatibility h s hs htor hu additivity L p q
  exact ⟨x, (objectCondition_iff D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality p x.1).mpr ⟨hx, hn⟩, hq⟩

/-- Equality retains the actual inverse, polarization multiplier and compatible-orbit equation. -/
theorem classOf_eq_iff {U : Level} (x y : Data U)
    (hx : Condition x.1) (hy : Condition y.1) :
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
  exact HarrisNumericalWeilLevel.classOf_eq_iff D C hΦ preservation composition
    unitCoherence associativity comparison symmetry stability square universality b
    compatibility h s hs htor hu additivity L p x y
    ((objectCondition_iff D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p x.1).mp hx).1
    ((objectCondition_iff D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p y.1).mp hy).1
    ((objectCondition_iff D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p x.1).mp hx).2
    ((objectCondition_iff D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p y.1).mp hy).2

/-- The existing actual original-group representative map changes only its level orbit. -/
abbrev mapRepresentative {U V : Level} (f : U ⟶ V) (x : Data U) : Data V :=
  HarrisNumericalWeilLevel.mapRepresentative D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h s hs htor hu f x

local notation "mapRep" => mapRepresentative D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu

/-- The same actual object supplies both conditions before and after every level arrow. -/
theorem objectCondition_mapRepresentative {U V : Level} (f : U ⟶ V) (x : Data U) :
    Condition (mapRep f x).1 ↔ Condition x.1 := Iff.rfl

/-- The genuine original-group transporter functor at the CM-induced reflex base. -/
abbrev isoClassTower : Level ⥤ Type 1 :=
  HarrisNumericalWeilLevel.isoClassTower D C hΦ preservation composition unitCoherence
    associativity comparison symmetry stability square universality b compatibility h
    s hs htor hu additivity L p

local notation "tower" => isoClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h
  s hs htor hu additivity

/-- The actual transition map of the specialized tower. -/
def classMap {U V : Level} (f : U ⟶ V) (q : Classes U) : Classes V :=
  (tower).map f q

local notation "mapClass" => classMap D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h
  s hs htor hu additivity

@[simp] theorem classMap_classOf {U V : Level} (f : U ⟶ V)
    (x : Data U) (hx : Condition x.1) :
    mapClass f (mkClass x hx) = mkClass (mapRep f x) hx := rfl

@[simp] theorem classMap_id (U : Level) (q : Classes U) :
    mapClass (𝟙 U) q = q :=
  ConcreteCategory.congr_hom ((tower).map_id U) q

theorem classMap_comp {U V W : Level} (f : U ⟶ V) (g : V ⟶ W) (q : Classes U) :
    mapClass (f ≫ g) q = mapClass g (mapClass f q) :=
  ConcreteCategory.congr_hom ((tower).map_comp f g) q

local notation "ambientTower" => harrisIsoClassTower D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality b
  compatibility h s hs htor hu additivity

/-- Natural inclusion into the polarized determinant tower at the constructed reflex base. -/
def inclusionNatTrans : tower ⟶ ambientTower :=
  HarrisNumericalWeilLevel.inclusionNatTrans D C hΦ preservation composition unitCoherence
    associativity comparison symmetry stability square universality b compatibility h
    s hs htor hu additivity L p

/-- The actual inclusion is injective at every original compact-open level. -/
theorem inclusion_injective (U : Level) :
    Function.Injective
      ((inclusionNatTrans D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality p compatibility h
        s hs htor hu additivity).app U) :=
  Subtype.val_injective

/-- Forget polarization and level while retaining the actual numerical action-class image. -/
def forgetNumericalAction {U : Level} (q : Classes U) :
    HarrisTaylor.NumericalActionClass L F p n E (A := A) :=
  HarrisNumericalWeilLevel.forgetNumericalAction D C hΦ preservation composition
    unitCoherence associativity comparison symmetry stability square universality b
    compatibility h s hs htor hu additivity L p q

local notation "forgetNum" => forgetNumericalAction D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h
  s hs htor hu additivity

@[simp] theorem forgetNumericalAction_classOf {U : Level}
    (x : Data U) (hx : Condition x.1) :
    letI := auxiliaryStarRing D C
    forgetNum (mkClass x hx) = HarrisTaylor.numericalActionClassOf L F p n E
      x.1.actionObj
      ((objectCondition_iff D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality p x.1).mp hx).2 := rfl

/-- The numerical action class is constant along every actual original level arrow. -/
theorem forgetNumericalAction_classMap {U V : Level} (f : U ⟶ V) (q : Classes U) :
    forgetNum (mapClass f q) = forgetNum q :=
  HarrisNumericalWeilLevel.forgetNumericalAction_classMap D C hΦ preservation composition
    unitCoherence associativity comparison symmetry stability square universality b
    compatibility h s hs htor hu additivity L p f q

/-- The specialized forgetful maps form the proved natural transformation. -/
def forgetNumericalActionNatTrans :
    tower ⟶ (Functor.const Level).obj
      (HarrisTaylor.NumericalActionClass L F p n E (A := A)) :=
  HarrisNumericalWeilLevel.forgetNumericalActionNatTrans D C hΦ preservation composition
    unitCoherence associativity comparison symmetry stability square universality b
    compatibility h s hs htor hu additivity L p

/-- Forget an original compact-open subgroup using its actual inclusion arrow. -/
def forgetLevel {U V : Level} (hU : U.subgroup ≤ V.subgroup) :
    Classes U → Classes V := mapClass (CompactOpenLevel.inclusion hU)

@[simp] theorem forgetLevel_classOf {U V : Level} (hU : U.subgroup ≤ V.subgroup)
    (x : Data U) (hx : Condition x.1) :
    forgetLevel D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality p compatibility h s hs htor hu additivity hU
      (mkClass x hx) = mkClass (mapRep (CompactOpenLevel.inclusion hU) x) hx := rfl

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

/-- The right-translation leg from that same actual intersection. -/
def heckeRight (U V : Level) (g : OriginalGroup) :
    letI := rationalFinite D C
    Classes (CompactOpenLevel.heckeLevel U V g) → Classes V := by
  letI := rationalFinite D C
  exact fun q => mapClass (CompactOpenLevel.heckeRight U V g) q

@[simp] theorem heckeLeft_classOf (U V : Level) (g : OriginalGroup)
    (x : letI := rationalFinite D C
      Data (CompactOpenLevel.heckeLevel U V g)) (hx : Condition x.1) :
    letI := rationalFinite D C
    heckeLeft D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality p compatibility h s hs htor hu additivity
      U V g (mkClass x hx) =
      mkClass (mapRep (CompactOpenLevel.heckeLeft U V g) x) hx := rfl

@[simp] theorem heckeRight_classOf (U V : Level) (g : OriginalGroup)
    (x : letI := rationalFinite D C
      Data (CompactOpenLevel.heckeLevel U V g)) (hx : Condition x.1) :
    letI := rationalFinite D C
    heckeRight D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality p compatibility h s hs htor hu additivity
      U V g (mkClass x hx) =
      mkClass (mapRep (CompactOpenLevel.heckeRight U V g) x) hx := rfl

omit hμfin hμet [QuasiSeparatedSpace S] in
/-- In the imaginary-quadratic rank-three case, the actual prescribed reflex
section coefficient at the normalized base is `-3*a` through the same `p`. -/
theorem normalizedReflexSection_rank_three [IsQuadraticExtension ℚ F]
    {τ₃ : F →+* ℂ}
    (C₃ : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap F F) τ₃))
    (hn : n = 3) (a : F) (ha : IsCMField.complexConj F a = -a) (U : S.Opens) :
    HodgeDeterminant.traceCoefficient
      (MvPolynomial.map (secHom (D.harrisTaylorReflexStructure C₃ p) U).hom
        (D.kottwitzReflexDeterminant C₃
          (isCMSection_harrisCMSection E (algebraMap F F) τ₃)
          ![1, algebraMap F A a])) = (secHom p U).hom (-3 * a) := by
  rw [D.traceCoefficient_reflexDeterminant_harrisTaylor_section C₃ p]
  change (secHom p U).hom (HarrisTaylor.lieTraceValue F F n a) = _
  apply congrArg (secHom p U).hom
  rw [← D.traceCoefficient_harrisTaylorCentralDeterminant C₃]
  exact D.traceCoefficient_harrisTaylorCentralDeterminant_rank_three C₃ hn a ha

end Langlands.Shimura.PEL.HarrisCMWeilLevel
