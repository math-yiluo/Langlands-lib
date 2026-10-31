import Langlands.Shimura.PEL.HarrisNumericalWeilTower
import Langlands.Shimura.PEL.HarrisCMWeilActionProjection
import Langlands.Shimura.PEL.HarrisTaylorCMActionPresheaf

/-! # Normalized CM specialization of the actual polarized numerical tower -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel HarrisNumericalWeilLevel
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
  {S : Scheme.{0}}
  (p : S ⟶ Spec (.of F))
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

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "reflexStructure" => D.harrisTaylorReflexStructure C p
local notation "Data" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu
local notation "Good" => PositiveObjectCondition D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality reflexStructure
local notation "Num" => NumericalObjectCondition D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
local notation "HarrisClasses" => HarrisIsoClass D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality reflexStructure
  compatibility h s hs htor hu additivity
local notation "Condition" => ClassCondition D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality reflexStructure
  compatibility h s hs htor hu additivity L p
local notation "Classes" => IsoClass D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality reflexStructure
  compatibility h s hs htor hu additivity L p
local notation "mkClass" => classOf D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality reflexStructure
  compatibility h s hs htor hu additivity L p
local notation "mkHarris" => harrisClassOf D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality reflexStructure
  compatibility h s hs htor hu additivity
local notation "mapClass" => classMap D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality reflexStructure
  compatibility h s hs htor hu additivity L p
local notation "tower" => isoClassTower D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality reflexStructure
  compatibility h s hs htor hu additivity L p

omit [IsCMField F] hμfin hμet [QuasiSeparatedSpace S] in
/-- The positive polarized determinant test uses the prescribed normalized CM scalar map. -/
theorem positiveObjectCondition_iff
    (X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := S)) :
    letI := auxiliaryStarRing D C
    Good X ↔ D.HarrisTaylorCMRationalLieDeterminantCondition C p
      X.actionObj.abelianScheme X.actionObj.action := by
  let := auxiliaryStarRing D C
  exact (D.harrisTaylorCMRationalLieDeterminantCondition_iff C p
    X.actionObj.abelianScheme X.actionObj.action).symm

omit hμfin hμet [QuasiSeparatedSpace S] in
/-- One normalized determinant-and-dimension representative carries both tower tests. -/
theorem determinantDimensionCondition_iff
    (X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := S)) :
    letI := auxiliaryStarRing D C
    D.HarrisTaylorCMDeterminantDimensionCondition C p
        X.actionObj.abelianScheme X.actionObj.action ↔ Good X ∧ Num X := by
  let := auxiliaryStarRing D C
  exact (D.harrisTaylorCMDeterminantDimensionCondition_iff C p
    X.actionObj.abelianScheme X.actionObj.action).trans
      (and_congr (positiveObjectCondition_iff D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality p X).symm Iff.rfl)

/-- In the normalized tower, the numerical image requires only actual geometric dimension:
the normalized determinant already forces the full central trace. -/
theorem classCondition_iff_dimension {U : HarrisLevel D} (q : HarrisClasses U) :
    letI := auxiliaryStarRing D C
    Condition q ↔ ∃ (x : Data U) (hx : Good x.1),
      mkHarris x hx = q ∧
        HarrisTaylor.PrescribedRelativeDimension E x.1.actionObj.abelianScheme n := by
  let := auxiliaryStarRing D C
  constructor
  · rintro ⟨x, hx, hq, hn⟩
    exact ⟨x, hx, hq, hn.1⟩
  · rintro ⟨x, hx, hq, hdim⟩
    refine ⟨x, hx, hq, hdim, ?_⟩
    exact D.harrisTaylorCMRationalLieDeterminantCondition_centralTrace C p
      x.1.actionObj.abelianScheme x.1.actionObj.action
      ((positiveObjectCondition_iff D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality p x.1).mp hx)

local notation "forgetNum" => forgetNumericalAction D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality reflexStructure
  compatibility h s hs htor hu additivity L p

/-- Forget the actual polarization and orbit into the joint normalized action-class image. -/
abbrev forgetCMAction {U : HarrisLevel D} (q : Classes U) :
    D.HarrisTaylorCMActionClass C p :=
  HarrisCMWeilLevel.forgetCMAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality p compatibility h
    s hs htor hu additivity q

local notation "forgetCM" => forgetCMAction D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h
  s hs htor hu additivity
local notation "jointProof" => determinantDimensionCondition_iff D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality p

@[simp] theorem forgetCMAction_val {U : HarrisLevel D} (q : Classes U) :
    (forgetCM q).val = (forgetNum q).val := rfl

/-- The joint action class uses the same actual satisfying polarized representative. -/
@[simp] theorem forgetCMAction_classOf {U : HarrisLevel D}
    (x : Data U) (hx : Good x.1) (hn : Num x.1) :
    letI := auxiliaryStarRing D C
    forgetCM (mkClass x hx hn) =
      D.harrisTaylorCMActionClassOf C p x.1.actionObj
        ((jointProof x.1).mpr ⟨hx, hn⟩) := by
  let := auxiliaryStarRing D C
  rfl

/-- All original Harris transporters leave the joint normalized action class unchanged. -/
theorem forgetCMAction_classMap {U V : HarrisLevel D}
    (f : U ⟶ V) (q : Classes U) :
    forgetCM (mapClass f q) = forgetCM q := by
  obtain ⟨x, hx, hn, hq⟩ := classOf_surjective D C hΦ preservation composition
    unitCoherence associativity comparison symmetry stability square universality reflexStructure
    compatibility h s hs htor hu additivity L p q
  rw [← hq]
  rfl

/-- Actual normalized action forgetting is natural on the original Harris level category. -/
abbrev forgetCMActionNatTrans :
    tower ⟶ (Functor.const (HarrisLevel D)).obj (D.HarrisTaylorCMActionClass C p) :=
  HarrisCMWeilLevel.forgetCMActionNatTrans D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality p compatibility h
    s hs htor hu additivity

/-- Every action representative of the forgotten class satisfies the normalized determinant. -/
theorem forgetCMAction_determinant {U : HarrisLevel D} (q : Classes U)
    (X : RationalAlgebraAction S A) (hX : RationalAlgebraAction.classOf X = (forgetCM q).val) :
    D.HarrisTaylorCMRationalLieDeterminantCondition C p X.abelianScheme X.action :=
  D.harrisTaylorCMActionClassCondition_determinant C p (forgetCM q).val
    (forgetCM q).property X hX

/-- The full central trace holds for every action representative of the forgotten class. -/
theorem forgetCMAction_centralTrace {U : HarrisLevel D} (q : Classes U)
    (X : RationalAlgebraAction S A) (hX : RationalAlgebraAction.classOf X = (forgetCM q).val) :
    HarrisTaylor.CentralLieTraceCondition L p X.abelianScheme X.action n :=
  D.harrisTaylorCMRationalLieDeterminantCondition_centralTrace C p X.abelianScheme X.action
    (forgetCMAction_determinant D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p compatibility h
      s hs htor hu additivity q X hX)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
