import Langlands.Shimura.PEL.HarrisTaylorCMKernelInjectivity
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Invertibility of the original CM kernel comparison under original etaleness -/

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

/-- Geometric Hom injectivity makes the actual scheme diagonal surjective.
Algebraic closures of the diagonal target's residue fields supply the tests. -/
private theorem diagonal_surjective_of_geometricHom_injective
    {X Y : Scheme} (f : X ⟶ Y)
    (hf : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω], Function.Injective
      (fun a : Spec (CommRingCat.of Ω) ⟶ X => a ≫ f)) :
    Surjective (pullback.diagonal f) := by
  constructor
  intro y
  let c := HarrisGeometricPoint.ofResidue (pullback f f) y
  have he : c.hom ≫ pullback.fst f f = c.hom ≫ pullback.snd f f := by
    apply hf c.Ω
    simp only [Category.assoc, pullback.condition]
  have hfac : (c.hom ≫ pullback.fst f f) ≫ pullback.diagonal f = c.hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id] using he
  let x : Spec (CommRingCat.of c.Ω) := Classical.arbitrary _
  refine ⟨(c.hom ≫ pullback.fst f f) x, ?_⟩
  calc
    pullback.diagonal f ((c.hom ≫ pullback.fst f f) x) = c.hom x :=
      congrArg (fun a : Spec (CommRingCat.of c.Ω) ⟶ pullback f f => a x) hfac
    _ = y := by
      change (pullback f f).fromSpecResidueField y _ = y
      exact Scheme.fromSpecResidueField_apply _ _

private theorem isIso_of_surjective_openImmersion {X Y : Scheme} (f : X ⟶ Y)
    [IsOpenImmersion f] (hf : Function.Surjective f) : IsIso f := by
  have : Epi f.base := (TopCat.epi_iff_surjective _).mpr hf
  exact IsOpenImmersion.isIso f

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
local notation "graph" => representedCMNormalGraph D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- Etaleness of the same original forgetting map makes every original
residual graph etale; no freeness or kernel-isomorphism premise is used. -/
theorem representedCMNormalGraph_etale
    [Etale (projection R U V hVU)] (g : SmallCMResidualGroup D U V) :
    Etale (graph R U V hVU g) := by
  have : Etale (graph R U V hVU g ≫ pullback.fst
      (projection R U V hVU) (projection R U V hVU)) := by
    rw [representedCMNormalGraph_fst]
    infer_instance
  exact Etale.of_comp _ (pullback.fst (projection R U V hVU) (projection R U V hVU))

/-- The exact original coproduct comparison is etale when original forgetting is. -/
theorem representedCMNormalKernelComparison_etale
    [Etale (projection R U V hVU)] : Etale (kernelComparison R U V hVU) := by
  apply IsZariskiLocalAtSource.sigmaDesc (P := @Etale)
  intro g
  exact representedCMNormalGraph_etale D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor R U V hVU g

/-- Object rigidity yields universal injectivity of the original comparison,
without an etaleness hypothesis. -/
theorem representedCMNormalKernelComparison_universallyInjective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) : UniversallyInjective (kernelComparison R U V hVU) := by
  apply (UniversallyInjective.iff_diagonal _).mpr
  apply diagonal_surjective_of_geometricHom_injective
  intro Ω _ _
  exact representedCMNormalKernelComparison_geometricHom_injective D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    R U V hVU existence geometry hRigid Ω

/-- With original etaleness, the surjective open diagonal is invertible,
so the original comparison is a scheme monomorphism. -/
theorem representedCMNormalKernelComparison_mono
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    [Etale (projection R U V hVU)] : Mono (kernelComparison R U V hVU) := by
  have : Etale (kernelComparison R U V hVU) :=
    representedCMNormalKernelComparison_etale D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R U V hVU
  have : UniversallyInjective (kernelComparison R U V hVU) :=
    representedCMNormalKernelComparison_universallyInjective D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor R U V hVU
      existence geometry hRigid
  have hd : Surjective (pullback.diagonal (kernelComparison R U V hVU)) :=
    (UniversallyInjective.iff_diagonal _).mp inferInstance
  have : IsIso (pullback.diagonal (kernelComparison R U V hVU)) :=
    isIso_of_surjective_openImmersion _ hd.surj
  exact (pullback.isIso_diagonal_iff _).mp inferInstance

/-- Original etaleness and explicit coarse-object rigidity prove invertibility
of the exact original kernel comparison. -/
theorem representedCMNormalKernelComparison_isIso
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    [Etale (projection R U V hVU)] : IsIso (kernelComparison R U V hVU) := by
  have : Etale (kernelComparison R U V hVU) :=
    representedCMNormalKernelComparison_etale D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R U V hVU
  have : Mono (kernelComparison R U V hVU) :=
    representedCMNormalKernelComparison_mono D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R U V hVU existence geometry hRigid
  have : IsOpenImmersion (kernelComparison R U V hVU) :=
    IsOpenImmersion.of_flat_of_mono _
  exact isIso_of_surjective_openImmersion _
    (representedCMNormalKernelComparison_surjective D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor R U V hVU
      existence geometry)

/-- An actual scheme isomorphism, whose hom is the same original comparison. -/
def representedCMNormalKernelIso
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    [Etale (projection R U V hVU)] : copies R U V ≅ kernelPair R U V hVU := by
  have : IsIso (kernelComparison R U V hVU) :=
    representedCMNormalKernelComparison_isIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R U V hVU existence geometry hRigid
  exact asIso (kernelComparison R U V hVU)

local notation "kernelIso" => representedCMNormalKernelIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- The forward morphism is exactly the pre-existing original comparison. -/
@[simp] theorem representedCMNormalKernelIso_hom
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    [Etale (projection R U V hVU)] :
    (kernelIso R U V hVU existence geometry hRigid).hom =
      kernelComparison R U V hVU := rfl

/-- On actual geometric-field morphisms, the inverse is the previously
constructed lift into the original residual summand. -/
theorem representedCMNormalKernelIso_inv_geometricHom
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    [Etale (projection R U V hVU)]
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (c : Spec (CommRingCat.of Ω) ⟶ kernelPair R U V hVU) :
    c ≫ (kernelIso R U V hVU existence geometry hRigid).inv =
      representedCMNormalKernelGeometricLift D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor
        R U V hVU existence geometry c := by
  apply representedCMNormalKernelComparison_geometricHom_injective D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    R U V hVU existence geometry hRigid Ω
  calc
    (c ≫ (kernelIso R U V hVU existence geometry hRigid).inv) ≫
        kernelComparison R U V hVU = c := by
      change (c ≫ (kernelIso R U V hVU existence geometry hRigid).inv) ≫
        (kernelIso R U V hVU existence geometry hRigid).hom = c
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = _ := (representedCMNormalKernelGeometricLift_comp D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry c).symm

local notation "chosenReps" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "chosenComparison" => cmNormalKernelComparison D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

/-- Etaleness of the exact comparison for the existing chosen CM tower. -/
theorem cmNormalKernelComparison_etale
    [Etale (projection (chosenReps q) U V hVU)] :
    Etale (chosenComparison q) :=
  representedCMNormalKernelComparison_etale D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor (chosenReps q) U V hVU

/-- Object rigidity gives universal injectivity for the identical chosen tower. -/
theorem cmNormalKernelComparison_universallyInjective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) : UniversallyInjective (chosenComparison q) :=
  representedCMNormalKernelComparison_universallyInjective D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry hRigid

/-- Monomorphism of the chosen original comparison under original etaleness. -/
theorem cmNormalKernelComparison_mono
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    [Etale (projection (chosenReps q) U V hVU)] :
    Mono (chosenComparison q) :=
  representedCMNormalKernelComparison_mono D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry hRigid

/-- Invertibility of the original chosen comparison, derived from original
etaleness and explicit coarse-object rigidity. -/
theorem cmNormalKernelComparison_isIso
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    [Etale (projection (chosenReps q) U V hVU)] :
    IsIso (chosenComparison q) :=
  representedCMNormalKernelComparison_isIso D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry hRigid

/-- The scheme isomorphism for precisely the representations used by
`cmSchemeTower` and `cmNormalKernelComparison`. -/
def cmNormalKernelIso
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    [Etale (projection (chosenReps q) U V hVU)] :
    copies (chosenReps q) U V ≅ kernelPair (chosenReps q) U V hVU :=
  kernelIso (chosenReps q) U V hVU existence geometry hRigid

/-- The chosen isomorphism has the original chosen comparison as its hom. -/
@[simp] theorem cmNormalKernelIso_hom
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    [Etale (projection (chosenReps q) U V hVU)] :
    (cmNormalKernelIso D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U V hVU q existence geometry
      hRigid).hom = chosenComparison q := rfl

/-- The chosen inverse induces the identical chosen geometric lift. -/
theorem cmNormalKernelIso_inv_geometricHom
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    [Etale (projection (chosenReps q) U V hVU)]
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (c : Spec (CommRingCat.of Ω) ⟶ kernelPair (chosenReps q) U V hVU) :
    c ≫ (cmNormalKernelIso D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U V hVU q existence geometry
      hRigid).inv =
      cmNormalKernelGeometricLift D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor U V hVU q existence geometry c :=
  representedCMNormalKernelIso_inv_geometricHom D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry hRigid c

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
