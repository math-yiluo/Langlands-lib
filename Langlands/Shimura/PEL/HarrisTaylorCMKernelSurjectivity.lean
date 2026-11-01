import Langlands.Shimura.PEL.HarrisTaylorCMSchemeTransitivity
import Langlands.Shimura.PEL.HarrisTaylorCMNormalKernelPair

/-! # Surjectivity of the original residual CM kernel comparison -/

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


variable {L : Type} [Field L] [NumberField L] [IsCMField L]
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


local notation "schemes" => representedCMSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "quotientAction" => representedCMNormalQuotientAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "projection" => representedCMNormalProjection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

variable (R : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)
  (U V : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

local notation "copies" => representedCMNormalCopies D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "kernelPair" => representedCMNormalKernelPair D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "kernelComparison" => representedCMNormalKernelComparison D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "translation" => representedCMGeometricTranslation D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

omit [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal] in
private theorem kernelPoint_coarse_eq {T : Scheme}
    (c : T ⟶ kernelPair R U V hVU) :
    (c ≫ pullback.fst (projection R U V hVU) (projection R U V hVU)) ≫
        projection R U V hVU =
      (c ≫ pullback.snd (projection R U V hVU) (projection R U V hVU)) ≫
        projection R U V hVU := by
  simp only [Category.assoc, pullback.condition]

/-- Lift an actual geometric-field map to the original kernel pair into the
summand indexed by its proved residual translation. -/
def representedCMNormalKernelGeometricLift
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (c : Spec (CommRingCat.of Ω) ⟶ kernelPair R U V hVU) :
    Spec (CommRingCat.of Ω) ⟶ copies R U V :=
  (c ≫ pullback.fst (projection R U V hVU) (projection R U V hVU)) ≫
    Sigma.ι (fun _ : SmallCMResidualGroup D U V => (schemes R).obj V)
      (translation R U V hVU existence geometry
        (c ≫ pullback.fst _ _) (c ≫ pullback.snd _ _)
        (kernelPoint_coarse_eq D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor R U V hVU c))

local notation "liftKernel" => representedCMNormalKernelGeometricLift D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- The constructed map lifts through the exact original kernel comparison. -/
@[reassoc (attr := simp)] theorem representedCMNormalKernelGeometricLift_comp
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (c : Spec (CommRingCat.of Ω) ⟶ kernelPair R U V hVU) :
    liftKernel R U V hVU existence geometry c ≫ kernelComparison R U V hVU = c := by
  apply pullback.hom_ext
  · simp only [representedCMNormalKernelGeometricLift, Category.assoc,
      representedCMNormalKernelComparison_ι_assoc, representedCMNormalGraph_fst,
      Category.comp_id]
  · simp only [representedCMNormalKernelGeometricLift, Category.assoc,
      representedCMNormalKernelComparison_ι_assoc, representedCMNormalGraph_snd]
    exact representedCMGeometricTranslation_action D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor R U V hVU
      existence geometry (c ≫ pullback.fst _ _) (c ≫ pullback.snd _ _)
      (kernelPoint_coarse_eq D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor R U V hVU c)

/-- Postcomposition by the original kernel comparison is surjective on actual
maps from every algebraically closed field spectrum. -/
theorem representedCMNormalKernelComparison_geometricHom_surjective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] :
    Function.Surjective
      (fun d : Spec (CommRingCat.of Ω) ⟶ copies R U V =>
        d ≫ kernelComparison R U V hVU) := by
  intro c
  exact ⟨liftKernel R U V hVU existence geometry c,
    representedCMNormalKernelGeometricLift_comp D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor R U V hVU
      existence geometry c⟩

/-- Algebraic closures of residue fields turn the proved geometric lifts into
surjectivity of the original kernel comparison on scheme points. -/
theorem representedCMNormalKernelComparison_surjective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    Function.Surjective (kernelComparison R U V hVU) := by
  intro y
  let c := HarrisGeometricPoint.ofResidue (kernelPair R U V hVU) y
  let x : Spec (CommRingCat.of c.Ω) := Classical.arbitrary _
  refine ⟨liftKernel R U V hVU existence geometry c.hom x, ?_⟩
  calc
    kernelComparison R U V hVU (liftKernel R U V hVU existence geometry c.hom x) =
        c.hom x := congrArg
      (fun d : Spec (CommRingCat.of c.Ω) ⟶ kernelPair R U V hVU => d x)
      (representedCMNormalKernelGeometricLift_comp D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor R U V hVU
        existence geometry c.hom)
    _ = y := by
      change (kernelPair R U V hVU).fromSpecResidueField y _ = y
      exact Scheme.fromSpecResidueField_apply _ _

local notation "chosenReps" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "chosenComparison" => cmNormalKernelComparison D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

/-- Specialize the actual kernel lift to the identical chosen representation
family defining `cmSchemeTower` and `cmNormalKernelComparison`. -/
def cmNormalKernelGeometricLift
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (c : Spec (CommRingCat.of Ω) ⟶ kernelPair (chosenReps q) U V hVU) :
    Spec (CommRingCat.of Ω) ⟶ copies (chosenReps q) U V :=
  liftKernel (chosenReps q) U V hVU existence geometry c

/-- The specialized lift composes with the exact original chosen comparison. -/
@[reassoc (attr := simp)] theorem cmNormalKernelGeometricLift_comp
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (c : Spec (CommRingCat.of Ω) ⟶ kernelPair (chosenReps q) U V hVU) :
    cmNormalKernelGeometricLift D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor U V hVU q existence geometry c ≫
      chosenComparison q = c :=
  representedCMNormalKernelGeometricLift_comp D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry c

/-- The existing chosen comparison is surjective on actual geometric-field Hom sets. -/
theorem cmNormalKernelComparison_geometricHom_surjective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] :
    Function.Surjective
      (fun d : Spec (CommRingCat.of Ω) ⟶ copies (chosenReps q) U V =>
        d ≫ chosenComparison q) :=
  representedCMNormalKernelComparison_geometricHom_surjective D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry Ω

/-- Surjectivity on points of the exact `cmNormalKernelComparison`, conditional
on precisely the existing representability and named dual assertions. -/
theorem cmNormalKernelComparison_surjective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    Function.Surjective (chosenComparison q) :=
  representedCMNormalKernelComparison_surjective D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
