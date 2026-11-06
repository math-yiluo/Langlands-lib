import Langlands.Shimura.PEL.PolarizedWeilIsogenyModel
import Langlands.Shimura.PEL.HarrisTaylorCMOrderModel

/-! # Harris CM conditions on an exact supplied rational isogeny model -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.PolarizedWeilLevel

open Langlands.AbelianScheme Langlands.AbelianScheme.PolarizedFiniteLevel

variable (P : Prerequisites.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S]
  {R : Type v} [Ring R] [Algebra ℚ R] [StarRing R]
  (X : PolarizedAction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality S R)
  (B : AbelianScheme S)
  (e : Rationalization.of B ≅ Rationalization.of X.actionObj.abelianScheme)
  {K : Type u} [Field K] [CharZero K] (p : S ⟶ Spec (.of K))

omit [QuasiSeparatedSpace S] in
include e p in
/-- The exact supplied rational model has every relative dimension of the
original abelian scheme, using the two actual etale integral representatives. -/
theorem PolarizedAction.isogenyModel_relativeDimension_iff (g : ℕ) :
    X.actionObj.abelianScheme.HasRelativeDimension g ↔ B.HasRelativeDimension g := by
  let d := PolarizedAction.isogenyInverseData (P := P) (X := X) (B := B) (e := e)
  have hmaps := integralInverseData_finiteEtaleIsogenies d
    (PolarizedAction.isogenyInverseData_pos (P := P) (X := X) (B := B) (e := e))
    (PolarizedAction.isogenyInverseData_unit
      (P := P) (X := X) (B := B) (e := e) (p := p))
  have : Etale (hom d.hom) := hmaps.2.1
  have : Etale (hom d.inv) := hmaps.2.2.2
  constructor
  · intro hA
    let : SmoothOfRelativeDimension g X.actionObj.abelianScheme.X.hom := hA
    have h : SmoothOfRelativeDimension (0 + g)
        (hom d.hom ≫ X.actionObj.abelianScheme.X.hom) := inferInstance
    simpa only [zero_add, Over.w] using h
  · intro hB
    let : SmoothOfRelativeDimension g B.X.hom := hB
    have h : SmoothOfRelativeDimension (0 + g) (hom d.inv ≫ B.X.hom) := inferInstance
    simpa only [zero_add, Over.w] using h

end Langlands.Shimura.PEL.PolarizedWeilLevel

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open HarrisPolarizedWeilLevel HarrisNumericalWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

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
  (Z : AdmissibleCMBaseCategory D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality)
  (X : PositivePolarizedAction D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    (S := Z.obj.left))

variable (B : AbelianScheme Z.obj.left)
variable (e : letI := auxiliaryStarRing D C
  Rationalization.of B ≅ Rationalization.of X.actionObj.abelianScheme)

/-- The admissible base supplies actual dual data on the very supplied model. -/
def cmIsogenyModelDualWitness : DualWitness B := by
  let W := Classical.choice (Z.property.dualExists B)
  exact ⟨W.hasDual, W.geometry, W.inversePoincare, W.evaluation⟩

local notation "dualModel" => cmIsogenyModelDualWitness D C P Z B

/-- Equip the supplied rational model with its conjugate faithful action and
actual polarization for the original positive auxiliary involution. -/
def cmPolarizedIsogenyModel :
    PositivePolarizedAction D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      (S := Z.obj.left) := by
  letI := auxiliaryStarRing D C
  exact PolarizedWeilLevel.PolarizedAction.isogenyModel
    (P := P) (X := X) (B := B) (e := e) (W := dualModel) (p := Z.obj.hom)

local notation "Y" => cmPolarizedIsogenyModel D C P Z X B e

/-- The comparison to this exact model retains the supplied inverse. -/
def cmPolarizedIsogenyModelIso :
    letI := auxiliaryStarRing D C
    X.actionObj ≅ (Y).actionObj := by
  letI := auxiliaryStarRing D C
  exact PolarizedWeilLevel.PolarizedAction.isogenyModelIso
    (P := P) (X := X) (B := B) (e := e) (W := dualModel) (p := Z.obj.hom)

omit [IsCMField F] [IsScalarTower ℚ F A] in
@[simp] theorem cmPolarizedIsogenyModelIso_hom :
    letI := auxiliaryStarRing D C
    RationalAlgebraAction.hom0 (cmPolarizedIsogenyModelIso D C P Z X B e).hom = e.inv := by
  let := auxiliaryStarRing D C
  rfl

omit [IsCMField F] [IsScalarTower ℚ F A] in
@[simp] theorem cmPolarizedIsogenyModelIso_inv :
    letI := auxiliaryStarRing D C
    RationalAlgebraAction.hom0 (cmPolarizedIsogenyModelIso D C P Z X B e).inv = e.hom := by
  let := auxiliaryStarRing D C
  rfl

omit [IsCMField F] in
/-- The unchanged normalized CM determinant and actual dimension hold on the
exact conjugate model precisely when they hold on the original representative. -/
theorem cmPolarizedIsogenyModel_condition_iff :
    letI := auxiliaryStarRing D C
    D.HarrisTaylorCMDeterminantDimensionCondition C Z.obj.hom
        X.actionObj.abelianScheme X.actionObj.action ↔
      D.HarrisTaylorCMDeterminantDimensionCondition C Z.obj.hom
        (Y).actionObj.abelianScheme (Y).actionObj.action := by
  let := auxiliaryStarRing D C
  apply and_congr
  · exact D.harrisTaylorCMRationalLieDeterminantCondition_iso C Z.obj.hom
      X.actionObj.action (Y).actionObj.action
      (RationalAlgebraAction.underlyingIso (cmPolarizedIsogenyModelIso D C P Z X B e))
      (RationalAlgebraAction.intertwines (cmPolarizedIsogenyModelIso D C P Z X B e).hom)
  · exact PolarizedWeilLevel.PolarizedAction.isogenyModel_relativeDimension_iff
      (P := P) (X := X) (B := B) (e := e) (p := Z.obj.hom) _

/-- The multiplier scales the chosen polarization and leaves the comparison
arrows unchanged. -/
def cmPolarizedIsogenyModelMultiplier : ℚˣ :=
  letI := auxiliaryStarRing D C
  let d := PolarizedWeilLevel.PolarizedAction.isogenyIntegralData
    (P := P) (X := X) (B := B) (e := e)
  Units.mk0 ((d.homDenom : ℚ) ^ 2)
    (pow_ne_zero _ (Int.cast_ne_zero.mpr d.homDenom_ne_zero))

local notation "q" => cmPolarizedIsogenyModelMultiplier D C P Z X B e

omit [IsCMField F] [IsScalarTower ℚ F A] in
theorem cmPolarizedIsogenyModelMultiplier_pos : 0 < (q : ℚ) := by
  let := auxiliaryStarRing D C
  exact PolarizedWeilLevel.PolarizedAction.isogenyModelMultiple_pos
    (P := P) (X := X) (B := B) (e := e)

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The original inverse and this positive square satisfy the actual
polarization equation in the original class relation. -/
theorem cmPolarizedIsogenyModel_multiple :
    letI := auxiliaryStarRing D C
    PolarizedWeilLevel.Multiple P.preservation P.composition P.unitCoherence P.associativity
      P.comparison P.symmetry P.stability P.square P.universality Z.property.pairAdditivity
      X Y q (cmPolarizedIsogenyModelIso D C P Z X B e) := by
  let := auxiliaryStarRing D C
  exact PolarizedWeilLevel.PolarizedAction.isogenyModelMultiple
    (P := P) (X := X) (B := B) (e := e) (W := dualModel) (p := Z.obj.hom)
    Z.property.pairAdditivity

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
