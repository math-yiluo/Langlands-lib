import Langlands.Shimura.PEL.HarrisTaylorCMTateBaseChange
import Langlands.Shimura.PEL.HarrisTaylorCMTateGeometricFamilies

/-! # The fixed-level presheaf of full Tate-normalized CM models -/

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
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

local notation "Bases" => AdmissibleCMBaseCategory D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
local notation "Family" => TateNormalizedCMGeometricFamily D C P compatibility h htor
local notation "forgetFamily" => tateNormalizedCMFamilyForget D C P compatibility h htor
local notation "oldPull" => unpointedClassTowerPullback D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  dualityNaturality polarizationStability compatibility h htor
local notation "oldPresheaf" => unpointedClassTowerPresheaf D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  dualityNaturality polarizationStability compatibility h htor
local notation "pointPull" => tateNormalizedCMClassBaseChange D C P
  dualityNaturality polarizationStability compatibility h htor

/-- Pull back actual normalized quotient classes at every pushed geometric point. -/
def tateNormalizedCMFamilyPullback {X Y : Bases} (f : Y ⟶ X) (U : HarrisLevel D) :
    Family X U → Family Y U :=
  fun x => ⟨fun a => pointPull f a U (x.val (a.comp f.hom.left)), by
    intro a b
    apply tateNormalizedCMForget_injective D C P Y compatibility h b.hom b.finiteFibers htor
    rw [tateNormalizedCMForget_geometricComparison,
      tateNormalizedCMForget_baseChange, tateNormalizedCMForget_baseChange]
    exact ((oldPull f).app U (forgetFamily X U x)).property a b⟩

local notation "pull" => tateNormalizedCMFamilyPullback D C P
  dualityNaturality polarizationStability compatibility h htor

/-- Forgetting the actual normalized family pullback gives the original family pullback. -/
@[simp] theorem tateNormalizedCMFamilyForget_pullback {X Y : Bases} (f : Y ⟶ X)
    (U : HarrisLevel D) (x : Family X U) :
    forgetFamily Y U (pull f U x) = (oldPull f).app U (forgetFamily X U x) := by
  apply Subtype.ext
  funext a
  exact tateNormalizedCMForget_baseChange D C P dualityNaturality polarizationStability
    compatibility h htor f a U (x.val (a.comp f.hom.left))

/-- Actual normalized family pullback along an identity is the identity. -/
@[simp] theorem tateNormalizedCMFamilyPullback_id (X : Bases) (U : HarrisLevel D)
    (x : Family X U) : pull (𝟙 X) U x = x := by
  apply tateNormalizedCMFamilyForget_injective D C P compatibility h htor X U
  rw [tateNormalizedCMFamilyForget_pullback, unpointedClassTowerPullback_id]
  rfl

/-- Actual normalized family pullbacks compose on the full connected base category. -/
theorem tateNormalizedCMFamilyPullback_comp {X Y Z : Bases}
    (f : Y ⟶ X) (g : Z ⟶ Y) (U : HarrisLevel D) (x : Family X U) :
    pull g U (pull f U x) = pull (g ≫ f) U x := by
  apply tateNormalizedCMFamilyForget_injective D C P compatibility h htor Z U
  simp only [tateNormalizedCMFamilyForget_pullback]
  exact congrArg (fun k => k.app U (forgetFamily X U x))
    (unpointedClassTowerPullback_comp D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      dualityNaturality polarizationStability compatibility h htor f g)

/-- At a fixed original level, normalized models form a presheaf on every
actual morphism of connected admissible CM bases. -/
def tateNormalizedCMUnpointedPresheaf (U : HarrisLevel D) : Basesᵒᵖ ⥤ Type 1 where
  obj X := Family X.unop U
  map f := ↾(pull f.unop U)
  map_id X := by
    ext x
    exact tateNormalizedCMFamilyPullback_id D C P dualityNaturality
      polarizationStability compatibility h htor X.unop U x
  map_comp f g := by
    ext x
    exact (tateNormalizedCMFamilyPullback_comp D C P dualityNaturality
      polarizationStability compatibility h htor f.unop g.unop U x).symm

local notation "presheaf" => tateNormalizedCMUnpointedPresheaf D C P
  dualityNaturality polarizationStability compatibility h htor

/-- Literal forgetting of normalized models is natural for every actual base map. -/
def tateNormalizedCMUnpointedForget (U : HarrisLevel D) :
    presheaf U ⟶ (oldPresheaf).flip.obj U where
  app X := ↾(forgetFamily X.unop U)
  naturality X Y f := by
    ext x
    exact tateNormalizedCMFamilyForget_pullback D C P dualityNaturality
      polarizationStability compatibility h htor f.unop U x

section Existence

variable (fibreAmple : ProperFibreAmpleAffineOpenStatement.{0})
  (realize : Tate.CommensurableInvariantLatticeRealizationStatement.{0})

/-- At a source-stabilizing level the existing conditional model existence
upgrades literal forgetting to a natural comparison with the original presheaf. -/
def tateNormalizedCMUnpointedIso (U : HarrisLevel D)
    (hU : ((hodgeLevelFunctor D C).obj U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    presheaf U ≅ (oldPresheaf).flip.obj U :=
  NatIso.ofComponents (fun X =>
    (tateNormalizedCMGeometricFamilyEquiv D C P compatibility h htor
      fibreAmple realize X.unop U hU).toIso) (by
    intro X Y f
    ext x
    exact tateNormalizedCMFamilyForget_pullback D C P dualityNaturality
      polarizationStability compatibility h htor f.unop U x)

/-- The natural comparison uses precisely the literal forgetful transformation. -/
@[simp] theorem tateNormalizedCMUnpointedIso_hom (U : HarrisLevel D)
    (hU : ((hodgeLevelFunctor D C).obj U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    (tateNormalizedCMUnpointedIso D C P dualityNaturality polarizationStability
      compatibility h htor fibreAmple realize U hU).hom =
    tateNormalizedCMUnpointedForget D C P dualityNaturality polarizationStability
      compatibility h htor U := rfl

end Existence

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
