import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedClasses
import Langlands.Shimura.PEL.HarrisIntegralOrderActions
import Langlands.Shimura.PEL.PolarizedWeilIntegralClasses

/-! # Exact integral witnesses in the normalized CM class relation -/

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
local notation "mkClass" => classOf D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality reflexStructure
  compatibility h s hs htor hu additivity L p
local notation "jointProof" => determinantDimensionCondition_iff D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality p
local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "basisO" => D.harrisHodgePELIntegralBasis C
local notation "Restriction" => PolarizedWeilLevel.IntegralActionRestriction preservation
  composition unitCoherence associativity comparison symmetry stability square universality
local notation "IntegralMult" => PolarizedWeilLevel.IntegralPolarizedMultiple preservation
  composition unitCoherence associativity comparison symmetry stability square universality
local notation "restore" => PolarizedWeilLevel.multiple_iff_integralPolarizedMultiple
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality basisO additivity
local notation "transport" => PolarizedWeilLevel.levelIso preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h A (D.harrisHodgePELForm C) s hs htor hu additivity

/-- On the same normalized determinant-and-dimension representatives, the original
CM class relation has exact integral action and polarization witnesses and retains
its actual rational-isomorphism level transport. -/
theorem classOf_eq_iff_integralPolarizedMultiple {U : HarrisLevel D} (x y : Data U)
    (hx : letI := auxiliaryStarRing D C
      D.HarrisTaylorCMDeterminantDimensionCondition C p
        x.1.actionObj.abelianScheme x.1.actionObj.action)
    (hy : letI := auxiliaryStarRing D C
      D.HarrisTaylorCMDeterminantDimensionCondition C p
        y.1.actionObj.abelianScheme y.1.actionObj.action)
    (a : letI := auxiliaryStarRing D C; Restriction O x.1)
    (a' : letI := auxiliaryStarRing D C; Restriction O y.1) :
    letI := auxiliaryStarRing D C
    mkClass x ((jointProof x.1).mp hx).1 ((jointProof x.1).mp hx).2 =
        mkClass y ((jointProof y.1).mp hy).1 ((jointProof y.1).mp hy).2 ↔
      ∃ (q : ℚˣ) (e : x.1.actionObj ≅ y.1.actionObj)
        (hd : IntegralMult x.1 y.1 a a' q e),
        transport x.1 y.1 ((hodgeLevelFunctor D C).obj U) q e
          ((restore x.1 y.1 a a' q e).mpr hd) x.2 = y.2 := by
  let := auxiliaryStarRing D C
  rw [HarrisNumericalWeilLevel.classOf_eq_iff]
  constructor
  · rintro ⟨q, e, he, hxy⟩
    exact ⟨q, e, (restore x.1 y.1 a a' q e).mp he, hxy⟩
  · rintro ⟨q, e, hd, hxy⟩
    exact ⟨q, e, (restore x.1 y.1 a a' q e).mpr hd, hxy⟩

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
