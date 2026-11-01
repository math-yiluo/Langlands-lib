import Langlands.AlgebraicGeometry.LocallyNoetherianComponentCoproduct
import Langlands.Shimura.PEL.HarrisTaylorCMSchemeTestTransitivity

/-! # Original CM kernel lifts on all locally Noetherian scheme tests -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
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
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

open Langlands.AlgebraicGeometry

local notation "copies" => representedCMNormalCopies D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "kernelPair" => representedCMNormalKernelPair D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "kernelComparison" => representedCMNormalKernelComparison D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "connectedLift" => representedCMNormalKernelConnectedLift D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

variable (R : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)
  (U V : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

/-- Assemble the actual connected lifts over all open connected components of
an arbitrary locally Noetherian source scheme. -/
def representedCMNormalKernelComponentLift
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {T : Scheme.{0}} [IsLocallyNoetherian T]
    (c : T ⟶ kernelPair R U V hVU) : T ⟶ copies R U V :=
  componentDesc T (fun k =>
    connectedLift R U V hVU existence geometry (componentι T k ≫ c))

local notation "componentLift" => representedCMNormalKernelComponentLift D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- The lift restricts to the previously constructed lift on the identical
actual component scheme. -/
@[reassoc (attr := simp)] theorem representedCMNormalKernelComponentLift_restrict
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {T : Scheme.{0}} [IsLocallyNoetherian T]
    (c : T ⟶ kernelPair R U V hVU) (k : _root_.ConnectedComponents T) :
    componentι T k ≫ componentLift R U V hVU existence geometry c =
      connectedLift R U V hVU existence geometry (componentι T k ≫ c) := by
  exact componentι_componentDesc T _ k

/-- The assembled scheme morphism composes with the original comparison to
the given morphism, including on nonreduced and disconnected sources. -/
@[reassoc (attr := simp)] theorem representedCMNormalKernelComponentLift_comp
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {T : Scheme.{0}} [IsLocallyNoetherian T]
    (c : T ⟶ kernelPair R U V hVU) :
    componentLift R U V hVU existence geometry c ≫ kernelComparison R U V hVU = c := by
  apply component_hom_ext T
  intro k
  rw [← Category.assoc, representedCMNormalKernelComponentLift_restrict]
  exact representedCMNormalKernelConnectedLift_comp D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    R U V hVU existence geometry (componentι T k ≫ c)

/-- Postcomposition with the identical original comparison is surjective on
scheme Hom sets for every locally Noetherian source. -/
theorem representedCMNormalKernelComparison_locallyNoetherianHom_surjective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (T : Scheme.{0}) [IsLocallyNoetherian T] :
    Function.Surjective
      (fun d : T ⟶ copies R U V => d ≫ kernelComparison R U V hVU) := by
  intro c
  exact ⟨componentLift R U V hVU existence geometry c,
    representedCMNormalKernelComponentLift_comp D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor R U V hVU
      existence geometry c⟩

local notation "chosenReps" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "chosenConnectedLift" => cmNormalKernelConnectedLift D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU
local notation "chosenComparison" => cmNormalKernelComparison D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

/-- The assembled lift for precisely the representation family defining the
original chosen CM scheme tower. -/
def cmNormalKernelComponentLift
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {T : Scheme.{0}} [IsLocallyNoetherian T]
    (c : T ⟶ kernelPair (chosenReps q) U V hVU) :
    T ⟶ copies (chosenReps q) U V :=
  componentLift (chosenReps q) U V hVU existence geometry c

local notation "chosenLift" => cmNormalKernelComponentLift D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU q

/-- The chosen lift is literally the assembly of the existing chosen connected
lifts on the original open component schemes. -/
theorem cmNormalKernelComponentLift_eq
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {T : Scheme.{0}} [IsLocallyNoetherian T]
    (c : T ⟶ kernelPair (chosenReps q) U V hVU) :
    chosenLift existence geometry c =
      componentDesc T (fun k =>
        chosenConnectedLift q existence geometry (componentι T k ≫ c)) := rfl

@[reassoc (attr := simp)] theorem cmNormalKernelComponentLift_restrict
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {T : Scheme.{0}} [IsLocallyNoetherian T]
    (c : T ⟶ kernelPair (chosenReps q) U V hVU) (k : _root_.ConnectedComponents T) :
    componentι T k ≫ chosenLift existence geometry c =
      chosenConnectedLift q existence geometry (componentι T k ≫ c) :=
  representedCMNormalKernelComponentLift_restrict D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry c k

@[reassoc (attr := simp)] theorem cmNormalKernelComponentLift_comp
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {T : Scheme.{0}} [IsLocallyNoetherian T]
    (c : T ⟶ kernelPair (chosenReps q) U V hVU) :
    chosenLift existence geometry c ≫ chosenComparison q = c :=
  representedCMNormalKernelComponentLift_comp D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry c

/-- The exact chosen comparison is surjective on scheme Hom sets for every
locally Noetherian source, without connectedness or nonemptiness assumptions. -/
theorem cmNormalKernelComparison_locallyNoetherianHom_surjective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (T : Scheme.{0}) [IsLocallyNoetherian T] :
    Function.Surjective
      (fun d : T ⟶ copies (chosenReps q) U V => d ≫ chosenComparison q) :=
  representedCMNormalKernelComparison_locallyNoetherianHom_surjective D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry T

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
