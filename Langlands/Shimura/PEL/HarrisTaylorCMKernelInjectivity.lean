import Langlands.Shimura.PEL.HarrisTaylorCMSchemeStabilizers
import Langlands.Shimura.PEL.HarrisTaylorCMKernelSurjectivity

/-! # Geometric Hom bijections for the original CM kernel comparison -/

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

/-- Every actual field-spectrum morphism to a scheme coproduct factors
through an actual summand; this is an equality of scheme morphisms. -/
theorem specFieldHom_factor_coproduct {Ω : Type} [Field Ω]
    {I : Type} (X : I → Scheme)
    (d : Spec (CommRingCat.of Ω) ⟶ ∐ X) :
    ∃ i : I, ∃ a : Spec (CommRingCat.of Ω) ⟶ X i, a ≫ Sigma.ι X i = d := by
  obtain ⟨⟨i, y⟩, hy⟩ := (AlgebraicGeometry.sigmaMk X).surjective (d default)
  rw [AlgebraicGeometry.sigmaMk_mk] at hy
  have hrange : Set.range d ⊆ Set.range (Sigma.ι X i) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨y, hy.trans (congrArg d (Subsingleton.elim default z))⟩
  exact ⟨i, IsOpenImmersion.lift _ d hrange, IsOpenImmersion.lift_fac _ _ _⟩

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
local notation "Rigid" => CMGeometricCoarseRigidity D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor
local notation "liftKernel" => representedCMNormalKernelGeometricLift D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- Postcomposition by the exact original kernel comparison is injective
on actual geometric-field Hom sets, under explicit coarse-object rigidity. -/
theorem representedCMNormalKernelComparison_geometricHom_injective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] :
    Function.Injective
      (fun d : Spec (CommRingCat.of Ω) ⟶ copies R U V =>
        d ≫ kernelComparison R U V hVU) := by
  intro d e he
  obtain ⟨g, a, ha⟩ := specFieldHom_factor_coproduct
    (fun _ : SmallCMResidualGroup D U V => (schemes R).obj V) d
  obtain ⟨k, b, hb⟩ := specFieldHom_factor_coproduct
    (fun _ : SmallCMResidualGroup D U V => (schemes R).obj V) e
  rw [← ha, ← hb] at he
  have hab : a = b := by
    simpa only [Category.assoc, representedCMNormalKernelComparison_ι_assoc,
      representedCMNormalGraph_fst, Category.comp_id] using
      congrArg (fun c : Spec (CommRingCat.of Ω) ⟶ kernelPair R U V hVU =>
        c ≫ pullback.fst (projection R U V hVU) (projection R U V hVU)) he
  have hgk : g = k := by
    apply representedCMGeometricPoint_normalTranslate_injective D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry hRigid a
    rw [← hab] at he
    simpa only [Category.assoc, representedCMNormalKernelComparison_ι_assoc,
      representedCMNormalGraph_snd] using
      congrArg (fun c : Spec (CommRingCat.of Ω) ⟶ kernelPair R U V hVU =>
        c ≫ pullback.snd (projection R U V hVU) (projection R U V hVU)) he
  rw [← ha, ← hb, hab, hgk]

/-- The original kernel comparison induces a bijection of geometric Hom sets.
This does not assert that the scheme morphism is an isomorphism. -/
theorem representedCMNormalKernelComparison_geometricHom_bijective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] :
    Function.Bijective
      (fun d : Spec (CommRingCat.of Ω) ⟶ copies R U V =>
        d ≫ kernelComparison R U V hVU) :=
  ⟨representedCMNormalKernelComparison_geometricHom_injective D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    R U V hVU existence geometry hRigid Ω,
   representedCMNormalKernelComparison_geometricHom_surjective D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    R U V hVU existence geometry Ω⟩

/-- The exact original comparison and the previously constructed actual
geometric lift are inverse on maps from every algebraically closed field. -/
def representedCMNormalKernelGeometricHomEquiv
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] :
    (Spec (CommRingCat.of Ω) ⟶ copies R U V) ≃
      (Spec (CommRingCat.of Ω) ⟶ kernelPair R U V hVU) where
  toFun d := d ≫ kernelComparison R U V hVU
  invFun c := liftKernel R U V hVU existence geometry c
  left_inv d := by
    apply representedCMNormalKernelComparison_geometricHom_injective D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry hRigid Ω
    exact representedCMNormalKernelGeometricLift_comp D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor R U V hVU
      existence geometry (d ≫ kernelComparison R U V hVU)
  right_inv c := representedCMNormalKernelGeometricLift_comp D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor R U V hVU
    existence geometry c

local notation "kernelEquiv" => representedCMNormalKernelGeometricHomEquiv D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- The forward function remains postcomposition with the original comparison. -/
@[simp] theorem representedCMNormalKernelGeometricHomEquiv_apply
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (d : Spec (CommRingCat.of Ω) ⟶ copies R U V) :
    kernelEquiv R U V hVU existence geometry hRigid Ω d =
      d ≫ kernelComparison R U V hVU := rfl

/-- The inverse remains the previously defined original geometric lift. -/
@[simp] theorem representedCMNormalKernelGeometricHomEquiv_symm_apply
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (c : Spec (CommRingCat.of Ω) ⟶ kernelPair R U V hVU) :
    (kernelEquiv R U V hVU existence geometry hRigid Ω).symm c =
      liftKernel R U V hVU existence geometry c := rfl

local notation "chosenReps" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "chosenComparison" => cmNormalKernelComparison D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

/-- Injectivity for precisely the chosen comparison defining the CM scheme tower. -/
theorem cmNormalKernelComparison_geometricHom_injective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] :
    Function.Injective
      (fun d : Spec (CommRingCat.of Ω) ⟶ copies (chosenReps q) U V =>
        d ≫ chosenComparison q) :=
  representedCMNormalKernelComparison_geometricHom_injective D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry hRigid Ω

/-- Bijectivity for precisely the existing chosen CM kernel comparison. -/
theorem cmNormalKernelComparison_geometricHom_bijective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] :
    Function.Bijective
      (fun d : Spec (CommRingCat.of Ω) ⟶ copies (chosenReps q) U V =>
        d ≫ chosenComparison q) :=
  representedCMNormalKernelComparison_geometricHom_bijective D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry hRigid Ω

/-- Specialize the Hom equivalence to the identical chosen representations
used by `cmSchemeTower` and `cmNormalKernelComparison`. -/
def cmNormalKernelGeometricHomEquiv
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] :
    (Spec (CommRingCat.of Ω) ⟶ copies (chosenReps q) U V) ≃
      (Spec (CommRingCat.of Ω) ⟶ kernelPair (chosenReps q) U V hVU) :=
  kernelEquiv (chosenReps q) U V hVU existence geometry hRigid Ω

/-- The chosen forward function is exactly the original chosen comparison. -/
@[simp] theorem cmNormalKernelGeometricHomEquiv_apply
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (d : Spec (CommRingCat.of Ω) ⟶ copies (chosenReps q) U V) :
    cmNormalKernelGeometricHomEquiv D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor U V hVU q existence geometry
        hRigid Ω d = d ≫ chosenComparison q := rfl

/-- The chosen inverse uses the original chosen geometric lift. -/
@[simp] theorem cmNormalKernelGeometricHomEquiv_symm_apply
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (c : Spec (CommRingCat.of Ω) ⟶ kernelPair (chosenReps q) U V hVU) :
    (cmNormalKernelGeometricHomEquiv D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor U V hVU q existence geometry
        hRigid Ω).symm c =
      cmNormalKernelGeometricLift D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor U V hVU q existence geometry c := rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
