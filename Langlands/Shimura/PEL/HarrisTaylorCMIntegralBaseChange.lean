import Langlands.Shimura.PEL.HarrisIntegralLevelBaseChange
import Langlands.Shimura.PEL.HarrisTaylorCMIntegralClasses
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedBaseChange

/-! # Normalized CM comparison with transported integral orbit witnesses -/

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

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "reflexS" => D.harrisTaylorReflexStructure C p
local notation "reflexT" => D.harrisTaylorReflexStructure C (b ≫ p)
local notation "GoodS" => PositiveObjectCondition D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality reflexS
local notation "GoodT" => PositiveObjectCondition D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality reflexT
local notation "NumS" => HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality L p
local notation "NumT" => HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality L (b ≫ p)

include lieNaturality

omit [IsCMField F] in
/-- The same actual changed representative satisfies the full normalized CM test. -/
theorem levelDataBaseChange_determinantDimensionCondition {U : HarrisLevel D}
    (x : DataS U)
    (hx : letI := auxiliaryStarRing D C
      D.HarrisTaylorCMDeterminantDimensionCondition C p
        x.1.actionObj.abelianScheme x.1.actionObj.action) :
    letI := auxiliaryStarRing D C
    D.HarrisTaylorCMDeterminantDimensionCondition C (b ≫ p)
      (pullData U x).1.actionObj.abelianScheme (pullData U x).1.actionObj.action := by
  let := auxiliaryStarRing D C
  exact D.harrisTaylorCMDeterminantDimensionCondition_baseChange_of_naturality C p
    x.1.actionObj.abelianScheme x.1.actionObj.action b lieNaturality hx

local notation "jointProof" => determinantDimensionCondition_iff D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality p
local notation "mkS" => HarrisNumericalWeilLevel.classOf D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality reflexS
  compatibility h (t ≫ b) hs htor huS addS L p
local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "basisO" => D.harrisHodgePELIntegralBasis C
local notation "Restriction" => PolarizedWeilLevel.IntegralActionRestriction preservation
  composition unitCoherence associativity comparison symmetry stability square universality
local notation "IntegralMult" => PolarizedWeilLevel.IntegralPolarizedMultiple preservation
  composition unitCoherence associativity comparison symmetry stability square universality
local notation "pullRestriction" => levelDataIntegralRestrictionBaseChange D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData
local notation "pullIntegral" => levelDataIntegralPolarizedMultiple_baseChange D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData
local notation "restoreT" => PolarizedWeilLevel.multiple_iff_integralPolarizedMultiple
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality basisO addT
local notation "transportT" => PolarizedWeilLevel.levelIso preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h A (D.harrisHodgePELForm C) t ht htor huT addT

omit lieNaturality in
/-- Equality of original normalized classes can be checked after pointed pullback
using integral witnesses and rational isomorphisms from the original representatives. -/
theorem classOf_eq_iff_exists_mappedIntegralPolarizedMultiple {U : HarrisLevel D}
    (x y : DataS U)
    (hx : letI := auxiliaryStarRing D C
      D.HarrisTaylorCMDeterminantDimensionCondition C p
        x.1.actionObj.abelianScheme x.1.actionObj.action)
    (hy : letI := auxiliaryStarRing D C
      D.HarrisTaylorCMDeterminantDimensionCondition C p
        y.1.actionObj.abelianScheme y.1.actionObj.action)
    (a : letI := auxiliaryStarRing D C; Restriction O x.1)
    (a' : letI := auxiliaryStarRing D C; Restriction O y.1) :
    letI := auxiliaryStarRing D C
    mkS x ((jointProof x.1).mp hx).1 ((jointProof x.1).mp hx).2 =
        mkS y ((jointProof y.1).mp hy).1 ((jointProof y.1).mp hy).2 ↔
      ∃ (q : ℚˣ) (e : x.1.actionObj ≅ y.1.actionObj)
        (hd : IntegralMult x.1 y.1 a a' q e),
        transportT (pullData U x).1 (pullData U y).1 ((indexFunctor).obj U) q
          ((RationalAlgebraAction.pullback b).mapIso e)
          ((restoreT (pullData U x).1 (pullData U y).1
            (pullRestriction x a) (pullRestriction y a') q
            ((RationalAlgebraAction.pullback b).mapIso e)).mpr
              (pullIntegral x y a a' q e hd))
          (pullData U x).2 = (pullData U y).2 := by
  let := auxiliaryStarRing D C
  rw [classOf_eq_iff_integralPolarizedMultiple D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality p
    compatibility h (t ≫ b) hs htor huS addS x y hx hy a a']
  constructor
  · rintro ⟨q, e, hd, hxy⟩
    refine ⟨q, e, hd, ?_⟩
    exact (levelDataIntegralPolarizedMultiple_levelIso_baseChange_iff D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability b compatibility h t ht hs htor
      huS huT dualData addS addT x y a a' q e hd).mp hxy
  · rintro ⟨q, e, hd, hxy⟩
    refine ⟨q, e, hd, ?_⟩
    exact (levelDataIntegralPolarizedMultiple_levelIso_baseChange_iff D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability b compatibility h t ht hs htor
      huS huT dualData addS addT x y a a' q e hd).mpr hxy

omit lieNaturality in
/-- Choose an original rational isomorphism with integral witnesses realizing a
normalized class equality, and retain its actual pulled-back orbit equation. -/
def mappedIntegralPolarizedWitnessOfClassEquality {U : HarrisLevel D}
    (x y : DataS U)
    (hx : letI := auxiliaryStarRing D C
      D.HarrisTaylorCMDeterminantDimensionCondition C p
        x.1.actionObj.abelianScheme x.1.actionObj.action)
    (hy : letI := auxiliaryStarRing D C
      D.HarrisTaylorCMDeterminantDimensionCondition C p
        y.1.actionObj.abelianScheme y.1.actionObj.action)
    (a : letI := auxiliaryStarRing D C; Restriction O x.1)
    (a' : letI := auxiliaryStarRing D C; Restriction O y.1) :
    letI := auxiliaryStarRing D C
    mkS x ((jointProof x.1).mp hx).1 ((jointProof x.1).mp hx).2 =
        mkS y ((jointProof y.1).mp hy).1 ((jointProof y.1).mp hy).2 →
      Σ (q : ℚˣ), Σ (e : x.1.actionObj ≅ y.1.actionObj),
        {hd : IntegralMult x.1 y.1 a a' q e //
          transportT (pullData U x).1 (pullData U y).1 ((indexFunctor).obj U) q
            ((RationalAlgebraAction.pullback b).mapIso e)
            ((restoreT (pullData U x).1 (pullData U y).1
              (pullRestriction x a) (pullRestriction y a') q
              ((RationalAlgebraAction.pullback b).mapIso e)).mpr
                (pullIntegral x y a a' q e hd))
            (pullData U x).2 = (pullData U y).2} := by
  let := auxiliaryStarRing D C
  intro hxy
  have hex := (classOf_eq_iff_exists_mappedIntegralPolarizedMultiple D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData
    p addS addT x y hx hy a a').mp hxy
  let q := Classical.choose hex
  have hq := Classical.choose_spec hex
  let e := Classical.choose hq
  have he := Classical.choose_spec hq
  exact ⟨q, e, Classical.choose he, Classical.choose_spec he⟩

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
