import Langlands.Shimura.PEL.HarrisTaylorCMTateClassComparison
import Langlands.Shimura.PEL.HarrisTaylorCMIntegralPointComparison
import Langlands.Shimura.PEL.HarrisIntegralNormalizationPointComparison

/-! # Actual point transport of full Tate-normalized CM models -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open HarrisPolarizedWeilLevel HarrisNumericalWeilLevel
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
  (P : Prerequisites.{0})
  (Z : AdmissibleCMBaseCategory D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality)
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

section Points

variable {Ω Ω' Ω'' : Type} [Field Ω] [Field Ω'] [Field Ω'']
  {s : Spec (.of Ω) ⟶ Z.obj.left} {t : Spec (.of Ω') ⟶ Z.obj.left}
  {r : Spec (.of Ω'') ⟶ Z.obj.left}
  {hs : ∀ Y : Cover Z.obj.left, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover Z.obj.left, Finite (Fiber t Y)}
  {hr : ∀ Y : Cover Z.obj.left, Finite (Fiber r Y)}

local notation "NRepAt" s₀:max hs₀:max =>
  TateNormalizedCMRepresentative D C P Z compatibility h s₀ hs₀ htor
local notation "NClassesAt" s₀:max hs₀:max =>
  TateNormalizedCMIsoClass D C P Z compatibility h s₀ hs₀ htor
local notation "repClassAt" s₀:max hs₀:max =>
  tateNormalizedCMRepresentativeClass D C P Z compatibility h s₀ hs₀ htor
local notation "forgetAt" s₀:max hs₀:max =>
  tateNormalizedCMForget D C P Z compatibility h s₀ hs₀ htor
local notation "relIffAt" s₀:max hs₀:max =>
  tateNormalizedCMRelated_iff_class_eq D C P Z compatibility h s₀ hs₀ htor
local notation "moveClass" => classPointMap D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  Z.obj.hom compatibility h htor Z.property.torsionUnits Z.property.pairAdditivity
local notation "moveTower" => classPointTowerIso D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  Z.obj.hom compatibility h htor Z.property.torsionUnits Z.property.pairAdditivity

/-- Change the geometric point by the original Tate transport, retaining the actual
abelian scheme, polarization, CM condition and integral order action. -/
def tateNormalizedCMRepresentativePointMap
    (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : HarrisLevel D) (x : (NRepAt s hs) U) : (NRepAt t ht) U := by
  let := auxiliaryStarRing D C
  exact {
    toIntegralCMRepresentative := integralCMRepresentativePointMap D C P.preservation
      P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
      P.square P.universality Z.obj.hom compatibility h htor Z.property.torsionUnits
      path U x.toIntegralCMRepresentative
    normalized := (harrisIntegralLevelCondition_point D C P compatibility h htor
      Z.property.torsionUnits x.data.1 path ((hodgeLevelFunctor D C).obj U) x.data.2).mpr
        x.normalized }

local notation "moveRep" => tateNormalizedCMRepresentativePointMap D C P Z
  compatibility h htor

/-- Forgetting the actual point-changed normalized model gives the original point map. -/
@[simp] theorem tateNormalizedCMRepresentativeClass_pointMap
    (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : HarrisLevel D) (x : (NRepAt s hs) U) :
    (repClassAt t ht) (moveRep path U x) = moveClass path U ((repClassAt s hs) x) := rfl

/-- Actual point transport preserves precisely the original quotient relation. -/
theorem tateNormalizedCMRelated_pointMap
    (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : HarrisLevel D) (x y : (NRepAt s hs) U)
    (hxy : TateNormalizedCMRelated D C P Z compatibility h s hs htor x y) :
    TateNormalizedCMRelated D C P Z compatibility h t ht htor
      (moveRep path U x) (moveRep path U y) := by
  apply (relIffAt t ht) _ _ |>.mpr
  simp only [tateNormalizedCMRepresentativeClass_pointMap]
  exact congrArg (moveClass path U) (((relIffAt s hs) x y).mp hxy)

/-- The original point comparison descends on actual normalized model classes. -/
def tateNormalizedCMClassPointMap (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : HarrisLevel D) : (NClassesAt s hs) U → (NClassesAt t ht) U :=
  Quotient.map (moveRep path U)
    (tateNormalizedCMRelated_pointMap D C P Z compatibility h htor path U)

local notation "move" => tateNormalizedCMClassPointMap D C P Z compatibility h htor

/-- The quotient map is the literal restriction of the original class point map. -/
@[simp] theorem tateNormalizedCMForget_pointMap
    (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : HarrisLevel D) (q : (NClassesAt s hs) U) :
    (forgetAt t ht) (move path U q) = moveClass path U ((forgetAt s hs) q) := by
  refine Quotient.inductionOn q ?_
  intro x
  rfl

/-- Reversing the actual path gives the inverse on normalized model classes. -/
def tateNormalizedCMClassPointEquiv (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : HarrisLevel D) : (NClassesAt s hs) U ≃ (NClassesAt t ht) U where
  toFun := move path U
  invFun := move path.symm U
  left_inv q := by
    apply tateNormalizedCMForget_injective D C P Z compatibility h s hs htor
    simp only [tateNormalizedCMForget_pointMap]
    exact (classPointEquiv D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      Z.obj.hom compatibility h htor Z.property.torsionUnits Z.property.pairAdditivity
      path U).left_inv ((forgetAt s hs) q)
  right_inv q := by
    apply tateNormalizedCMForget_injective D C P Z compatibility h t ht htor
    simp only [tateNormalizedCMForget_pointMap]
    exact (classPointEquiv D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      Z.obj.hom compatibility h htor Z.property.torsionUnits Z.property.pairAdditivity
      path U).right_inv ((forgetAt t ht) q)

/-- Different geometric paths induce the same normalized quotient map. -/
theorem tateNormalizedCMClassPointMap_path_independent
    (path path' : fiberFunctor s hs ≅ fiberFunctor t ht) (U : HarrisLevel D) :
    move path U = move path' U := by
  funext q
  apply tateNormalizedCMForget_injective D C P Z compatibility h t ht htor
  simp only [tateNormalizedCMForget_pointMap]
  exact congrArg (fun k => k.hom.app U ((forgetAt s hs) q))
    (classPointTowerIso_path_independent D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      Z.obj.hom compatibility h htor Z.property.torsionUnits Z.property.pairAdditivity
      path path')

@[simp] theorem tateNormalizedCMClassPointMap_refl (U : HarrisLevel D)
    (q : (NClassesAt s hs) U) :
    move (Iso.refl (fiberFunctor s hs)) U q = q := by
  apply tateNormalizedCMForget_injective D C P Z compatibility h s hs htor
  rw [tateNormalizedCMForget_pointMap]
  exact congrArg (fun k => k.hom.app U ((forgetAt s hs) q))
    (classPointTowerIso_refl D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      Z.obj.hom compatibility h htor Z.property.torsionUnits Z.property.pairAdditivity
      (s := s) (hs := hs))

/-- Composition is inherited from the original point comparison on the same classes. -/
theorem tateNormalizedCMClassPointMap_trans
    (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (path' : fiberFunctor t ht ≅ fiberFunctor r hr)
    (U : HarrisLevel D) (q : (NClassesAt s hs) U) :
    move (path ≪≫ path') U q = move path' U (move path U q) := by
  apply tateNormalizedCMForget_injective D C P Z compatibility h r hr htor
  simp only [tateNormalizedCMForget_pointMap]
  exact congrArg (fun k => k.hom.app U ((forgetAt s hs) q))
    (classPointTowerIso_trans D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      Z.obj.hom compatibility h htor Z.property.torsionUnits Z.property.pairAdditivity
      path path')

variable [IsAlgClosed Ω] [IsAlgClosed Ω']

/-- Canonical point independence is realized on actual full Tate-normalized classes. -/
def tateNormalizedCMClassGeometricPointEquiv (U : HarrisLevel D) :
    (NClassesAt s hs) U ≃ (NClassesAt t ht) U :=
  tateNormalizedCMClassPointEquiv D C P Z compatibility h htor
    (Classical.choice (geometricPathExists s t hs ht)) U

/-- Every geometric path computes the same canonical normalized comparison. -/
theorem tateNormalizedCMClassGeometricPointEquiv_eq_path
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) (U : HarrisLevel D) :
    tateNormalizedCMClassGeometricPointEquiv D C P Z compatibility h htor
      (s := s) (t := t) (hs := hs) (ht := ht) U =
    tateNormalizedCMClassPointEquiv D C P Z compatibility h htor path U := by
  apply Equiv.ext
  exact congrFun (tateNormalizedCMClassPointMap_path_independent D C P Z
    compatibility h htor _ path U)

end Points

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
