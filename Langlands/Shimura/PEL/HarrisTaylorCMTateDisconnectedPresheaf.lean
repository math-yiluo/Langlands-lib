import Langlands.Shimura.PEL.HarrisTaylorCMTateUnpointedPresheaf
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedDisconnectedPresheaf

/-! # Full Tate-normalized CM models on componentwise admissible bases -/

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
open Langlands.AlgebraicGeometry

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

local notation "DisBases" => ComponentwiseAdmissibleCMBaseCategory D C
  P.preservation P.composition P.unitCoherence P.associativity P.comparison
  P.symmetry P.stability P.square P.universality
local notation "component" => componentCMBase D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
local notation "componentHom" => componentCMBaseHomTo D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
local notation "Family" => TateNormalizedCMGeometricFamily D C P compatibility h htor
local notation "forgetFamily" => tateNormalizedCMFamilyForget D C P compatibility h htor
local notation "familyPull" => tateNormalizedCMFamilyPullback D C P
  dualityNaturality polarizationStability compatibility h htor
local notation "oldTower" => disconnectedClassTower D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h htor
local notation "oldPull" => disconnectedClassTowerPullback D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  dualityNaturality polarizationStability compatibility h htor
local notation "oldPresheaf" => disconnectedClassTowerPresheaf D C
  P.preservation P.composition P.unitCoherence P.associativity P.comparison
  P.symmetry P.stability P.square P.universality
  dualityNaturality polarizationStability compatibility h htor

/-- Products of actual normalized quotient families on the actual component schemes. -/
def TateNormalizedCMComponentwiseFamily (X : DisBases) (U : HarrisLevel D) : Type 1 :=
  ∀ c : _root_.ConnectedComponents X.obj.left, Family (component X c) U

local notation "DisFamily" => TateNormalizedCMComponentwiseFamily D C P compatibility h htor

/-- Forget normalized models on every actual connected component. -/
def tateNormalizedCMComponentwiseForget (X : DisBases) (U : HarrisLevel D) :
    DisFamily X U → (oldTower X).obj U :=
  fun x c => forgetFamily (component X c) U (x c)

local notation "forget" => tateNormalizedCMComponentwiseForget D C P compatibility h htor

/-- Componentwise forgetting reflects equality without assuming model existence. -/
theorem tateNormalizedCMComponentwiseForget_injective (X : DisBases) (U : HarrisLevel D) :
    Function.Injective (forget X U) := by
  intro x y hxy
  funext c
  apply tateNormalizedCMFamilyForget_injective D C P compatibility h htor (component X c) U
  exact congrArg (fun v => v c) hxy

/-- Pull back along the actual restricted morphism to each source component,
using the component selected by the original scheme morphism. -/
def tateNormalizedCMDisconnectedPullback {X Y : DisBases} (f : Y ⟶ X)
    (U : HarrisLevel D) : DisFamily X U → DisFamily Y U :=
  fun x c => familyPull (componentHom f c (componentMap f.hom.left c) rfl) U
    (x (componentMap f.hom.left c))

local notation "pull" => tateNormalizedCMDisconnectedPullback D C P
  dualityNaturality polarizationStability compatibility h htor

/-- The comparison square is the original disconnected pullback on the same components. -/
@[simp] theorem tateNormalizedCMComponentwiseForget_pullback {X Y : DisBases} (f : Y ⟶ X)
    (U : HarrisLevel D) (x : DisFamily X U) :
    forget Y U (pull f U x) = (oldPull f).app U (forget X U x) := by
  funext c
  exact tateNormalizedCMFamilyForget_pullback D C P dualityNaturality
    polarizationStability compatibility h htor
    (componentHom f c (componentMap f.hom.left c) rfl) U (x (componentMap f.hom.left c))

/-- Actual normalized componentwise pullback respects identity maps. -/
@[simp] theorem tateNormalizedCMDisconnectedPullback_id (X : DisBases) (U : HarrisLevel D)
    (x : DisFamily X U) : pull (𝟙 X) U x = x := by
  apply tateNormalizedCMComponentwiseForget_injective D C P compatibility h htor X U
  rw [tateNormalizedCMComponentwiseForget_pullback, disconnectedClassTowerPullback_id]
  rfl

/-- Actual normalized componentwise pullback composes for every original base map. -/
theorem tateNormalizedCMDisconnectedPullback_comp {X Y Z : DisBases}
    (f : Y ⟶ X) (g : Z ⟶ Y) (U : HarrisLevel D) (x : DisFamily X U) :
    pull g U (pull f U x) = pull (g ≫ f) U x := by
  apply tateNormalizedCMComponentwiseForget_injective D C P compatibility h htor Z U
  simp only [tateNormalizedCMComponentwiseForget_pullback]
  exact congrArg (fun k => k.app U (forget X U x))
    (disconnectedClassTowerPullback_comp D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      dualityNaturality polarizationStability compatibility h htor f g)

/-- The fixed-level normalized-model presheaf on the full original
componentwise admissible test category. -/
def tateNormalizedCMDisconnectedPresheaf (U : HarrisLevel D) : DisBasesᵒᵖ ⥤ Type 1 where
  obj X := DisFamily X.unop U
  map f := ↾(pull f.unop U)
  map_id X := by
    ext x
    exact tateNormalizedCMDisconnectedPullback_id D C P dualityNaturality
      polarizationStability compatibility h htor X.unop U x
  map_comp f g := by
    ext x
    exact (tateNormalizedCMDisconnectedPullback_comp D C P dualityNaturality
      polarizationStability compatibility h htor f.unop g.unop U x).symm

local notation "presheaf" => tateNormalizedCMDisconnectedPresheaf D C P
  dualityNaturality polarizationStability compatibility h htor

/-- The literal normalized-model forgetful transformation on every original test base. -/
def tateNormalizedCMDisconnectedForget (U : HarrisLevel D) :
    presheaf U ⟶ (oldPresheaf).flip.obj U where
  app X := ↾(forget X.unop U)
  naturality X Y f := by
    ext x
    exact tateNormalizedCMComponentwiseForget_pullback D C P dualityNaturality
      polarizationStability compatibility h htor f.unop U x

/-- An empty base has the unique empty-product normalized-model value. -/
abbrev tateNormalizedCMComponentwiseEmptyUnique (X : DisBases) [IsEmpty X.obj.left]
    (U : HarrisLevel D) : Unique (DisFamily X U) := by
  letI := componentIndex_isEmpty X.obj.left
  exact { default := fun c => isEmptyElim c, uniq := fun x => funext (fun c => isEmptyElim c) }

section Existence

variable (fibreAmple : ProperFibreAmpleAffineOpenStatement.{0})
  (realize : Tate.CommensurableInvariantLatticeRealizationStatement.{0})

/-- Conditional equivalence is componentwise literal forgetting of actual models. -/
def tateNormalizedCMComponentwiseEquiv (X : DisBases) (U : HarrisLevel D)
    (hU : ((hodgeLevelFunctor D C).obj U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    DisFamily X U ≃ (oldTower X).obj U :=
  Equiv.piCongrRight (fun c =>
    tateNormalizedCMGeometricFamilyEquiv D C P compatibility h htor
      fibreAmple realize (component X c) U hU)

/-- The conditional model comparison is natural on the full componentwise
admissible test category and uses the original disconnected CM presheaf. -/
def tateNormalizedCMDisconnectedIso (U : HarrisLevel D)
    (hU : ((hodgeLevelFunctor D C).obj U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    presheaf U ≅ (oldPresheaf).flip.obj U :=
  NatIso.ofComponents (fun X =>
    (tateNormalizedCMComponentwiseEquiv D C P compatibility h htor
      fibreAmple realize X.unop U hU).toIso) (by
    intro X Y f
    ext x
    exact tateNormalizedCMComponentwiseForget_pullback D C P dualityNaturality
      polarizationStability compatibility h htor f.unop U x)

/-- The full-category natural comparison has the literal forgetful forward map. -/
@[simp] theorem tateNormalizedCMDisconnectedIso_hom (U : HarrisLevel D)
    (hU : ((hodgeLevelFunctor D C).obj U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    (tateNormalizedCMDisconnectedIso D C P dualityNaturality polarizationStability
      compatibility h htor fibreAmple realize U hU).hom =
    tateNormalizedCMDisconnectedForget D C P dualityNaturality polarizationStability
      compatibility h htor U := rfl

end Existence

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
