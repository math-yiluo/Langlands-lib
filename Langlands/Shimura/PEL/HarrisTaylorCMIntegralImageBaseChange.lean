import Langlands.Shimura.PEL.HarrisTaylorCMIntegralClassImage
import Langlands.Shimura.PEL.HarrisTaylorCMIntegralBaseChange
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedAlignedBaseChange

/-! # Actual base change of the exact integral-action CM image -/

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
  {S T : Scheme.{0}} (b : T ⟶ S)

variable [QuasiSeparatedSpace S] [QuasiSeparatedSpace T]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (t : Spec (.of Ω) ⟶ T)
  (ht : ∀ Y : Cover T, Finite (Fiber t Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T k.val).X.hom]
  [hμetT : ∀ k : Index (fun _ => True), Etale (mu T k.val).X.hom]
  (dualData : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality b X)

local notation "DataS" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  (t ≫ b) hs htor huS
local notation "DataT" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  t ht htor huT
local notation "indexFunctor" => hodgeLevelFunctor D C

local notation "pullData" => levelDataBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData

variable (p : S ⟶ Spec (.of F))
  (lieNaturality : LieBaseChangeNaturalityStatement S)
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (addT : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T))

local notation "RepS" => IntegralCMRepresentative D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h (t ≫ b) hs htor huS
local notation "RepT" => IntegralCMRepresentative D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality (b ≫ p)
  compatibility h t ht htor huT
local notation "repClassS" => integralCMRepresentativeClass D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h (t ≫ b) hs htor huS addS
local notation "repClassT" => integralCMRepresentativeClass D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality (b ≫ p)
  compatibility h t ht htor huT addT
local notation "ConditionS" => IntegralCMClassCondition D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h (t ≫ b) hs htor huS addS
local notation "ConditionT" => IntegralCMClassCondition D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality (b ≫ p)
  compatibility h t ht htor huT addT
local notation "ImageS" => IntegralCMClassImage D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h (t ≫ b) hs htor huS addS
local notation "ImageT" => IntegralCMClassImage D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality (b ≫ p)
  compatibility h t ht htor huT addT
local notation "imageTowerS" => integralCMClassImageTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h (t ≫ b) hs htor huS addS
local notation "imageTowerT" => integralCMClassImageTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality (b ≫ p)
  compatibility h t ht htor huT addT
local notation "inclusionS" => integralCMClassImageInclusion D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h (t ≫ b) hs htor huS addS
local notation "inclusionT" => integralCMClassImageInclusion D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality (b ≫ p)
  compatibility h t ht htor huT addT
local notation "pullClass" => classBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData p lieNaturality addS addT
local notation "pullTower" => classTowerBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData p lieNaturality addS addT
local notation "pullRestriction" => levelDataIntegralRestrictionBaseChange D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData

/-- Pull back the same normalized representative and its supplied integral action. -/
def integralCMRepresentativeBaseChange (U : HarrisLevel D) (x : RepS U) : RepT U := by
  let := auxiliaryStarRing D C
  exact ⟨pullData U x.data,
    levelDataBaseChange_determinantDimensionCondition D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT
      dualData p lieNaturality x.data x.condition,
    pullRestriction x.data x.restriction⟩

local notation "pullRep" => integralCMRepresentativeBaseChange D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData
  p lieNaturality

/-- Forgetting the transported restriction gives the original actual CM class pullback. -/
@[simp] theorem integralCMRepresentativeClass_baseChange (U : HarrisLevel D) (x : RepS U) :
    repClassT (pullRep U x) = pullClass U (repClassS x) := rfl

/-- The exact integral-action image is preserved by arbitrary actual base change. -/
theorem integralCMClassCondition_baseChange (U : HarrisLevel D)
    (q : (HarrisNumericalWeilLevel.isoClassTower D C
      (isCMSection_harrisCMSection E (algebraMap L F) τ₀) preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      (D.harrisTaylorReflexStructure C p) compatibility h (t ≫ b) hs htor huS
      addS L p).obj U)
    (hq : ConditionS q) : ConditionT (pullClass U q) := by
  obtain ⟨x, hx⟩ := hq
  refine ⟨pullRep U x, ?_⟩
  rw [integralCMRepresentativeClass_baseChange]
  exact congrArg (pullClass U) hx

/-- Restrict the constructed normalized CM pullback to its exact integral-action image. -/
def integralCMClassImageBaseChange (U : HarrisLevel D) (q : ImageS U) : ImageT U :=
  ⟨pullClass U q.val,
    integralCMClassCondition_baseChange D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability b compatibility h t ht hs htor huS huT dualData p
      lieNaturality addS addT U q.val q.property⟩

local notation "pullImage" => integralCMClassImageBaseChange D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData
  p lieNaturality addS addT

/-- Image pullback is natural for every original Harris transporter. -/
def integralCMClassImageTowerBaseChange : imageTowerS ⟶ imageTowerT where
  app U := ↾(pullImage U)
  naturality {U V} f := by
    ext q
    apply Subtype.ext
    exact (pullTower).naturality_apply f q.val

local notation "pullImageTower" => integralCMClassImageTowerBaseChange D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData
  p lieNaturality addS addT

/-- The new map is the restriction of the existing normalized CM tower pullback. -/
theorem integralCMClassImageTowerBaseChange_inclusion :
    pullImageTower ≫ inclusionT = inclusionS ≫ pullTower := rfl

/-- The map on the actual image inherits independence from constrained dual choices. -/
theorem integralCMClassImageTowerBaseChange_dualData
    (dualData' : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := S),
      PositivePullbackDualData D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality b X) :
    pullImageTower =
      integralCMClassImageTowerBaseChange D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability b compatibility h t ht hs htor huS huT dualData'
        p lieNaturality addS addT := by
  ext U q
  apply Subtype.ext
  exact congrArg (fun k => k.app U q.val)
    (classTowerBaseChange_dualData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability b compatibility h t ht hs htor huS huT dualData dualData'
      p lieNaturality addS addT)

section Along
variable (q : T ⟶ Spec (.of F)) (s : Spec (.of Ω) ⟶ S)
  (hp : b ≫ p = q) (hsquare : t ≫ b = s)
  (hsource : ∀ Y : Cover S, Finite (Fiber s Y))

/-- Preserve the exact image along both commuting base triangles. -/
theorem integralCMClassCondition_baseChangeAlong (U : HarrisLevel D)
    (z : (HarrisNumericalWeilLevel.isoClassTower D C
      (isCMSection_harrisCMSection E (algebraMap L F) τ₀) preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      (D.harrisTaylorReflexStructure C p) compatibility h s hsource htor huS
      addS L p).obj U)
    (hz : IntegralCMClassCondition D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p compatibility h s hsource htor
      huS addS z) :
    IntegralCMClassCondition D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality q compatibility h t ht htor huT
      addT ((classTowerBaseChangeAlong D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor b p q s t hp hsquare hsource ht
        lieNaturality huS huT dualData addS addT).app U z) := by
  subst q s
  exact integralCMClassCondition_baseChange D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b compatibility h t ht hsource htor huS huT dualData
    p lieNaturality addS addT U z hz

end Along
end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
