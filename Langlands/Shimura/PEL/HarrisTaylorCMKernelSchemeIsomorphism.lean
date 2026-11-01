import Langlands.AlgebraicGeometry.ConnectedCoproductFactorization
import Langlands.Shimura.PEL.HarrisTaylorCMKernelSplitting
import Langlands.Shimura.PEL.HarrisTaylorCMKernelInjectivity

/-! # Original CM kernel scheme isomorphisms without an etaleness premise -/

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
variable (R : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)
  (U V : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

local notation "schemes" => representedCMSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "projection" => representedCMNormalProjection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "componentLift" => representedCMNormalKernelComponentLift D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

local notation "Rigid" => CMGeometricCoarseRigidity D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor
local notation "quotientAction" => representedCMNormalQuotientAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "graph" => representedCMNormalGraph D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "kernelSection" => representedCMNormalKernelSection D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- Geometric coarse rigidity determines the residual index of a lift on an
arbitrary connected source, while the first projection determines its map. -/
theorem representedCMNormalKernelComparison_connectedHom_injective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (T : Scheme.{0}) [ConnectedSpace T] :
    Function.Injective
      (fun d : T ⟶ copies R U V => d ≫ kernelComparison R U V hVU) := by
  intro d e he
  obtain ⟨g, a, ha⟩ := connectedHom_factor_coproduct
    (fun _ : SmallCMResidualGroup D U V => (schemes R).obj V) d
  obtain ⟨k, b, hb⟩ := connectedHom_factor_coproduct
    (fun _ : SmallCMResidualGroup D U V => (schemes R).obj V) e
  rw [← ha, ← hb] at he
  have hab : a = b := by
    simpa only [Category.assoc, representedCMNormalKernelComparison_ι_assoc,
      representedCMNormalGraph_fst, Category.comp_id] using
      congrArg (fun c : T ⟶ kernelPair R U V hVU =>
        c ≫ pullback.fst (projection R U V hVU) (projection R U V hVU)) he
  have hgk : g = k := by
    let z := HarrisGeometricPoint.ofResidue T (Classical.arbitrary T)
    apply representedCMGeometricPoint_normalTranslate_injective D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry hRigid (z.hom ≫ a)
    have hs : a ≫ (quotientAction R U V hVU).ρ g =
        a ≫ (quotientAction R U V hVU).ρ k := by
      rw [← hab] at he
      simpa only [Category.assoc, representedCMNormalKernelComparison_ι_assoc,
        representedCMNormalGraph_snd] using
        congrArg (fun c : T ⟶ kernelPair R U V hVU =>
          c ≫ pullback.snd (projection R U V hVU) (projection R U V hVU)) he
    simpa only [Category.assoc] using
      congrArg (fun f : T ⟶ (schemes R).obj V => z.hom ≫ f) hs
  rw [← ha, ← hb, hab, hgk]

/-- Actual component restrictions extend injectivity to all locally
Noetherian sources, including nonreduced and empty schemes. -/
theorem representedCMNormalKernelComparison_locallyNoetherianHom_injective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (T : Scheme.{0}) [IsLocallyNoetherian T] :
    Function.Injective
      (fun d : T ⟶ copies R U V => d ≫ kernelComparison R U V hVU) := by
  intro d e he
  apply component_hom_ext T
  intro k
  apply representedCMNormalKernelComparison_connectedHom_injective D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    R U V hVU existence geometry hRigid (componentScheme T k)
  simpa only [Category.assoc] using
    congrArg (fun c : T ⟶ kernelPair R U V hVU => componentι T k ≫ c) he

/-- The original copies scheme is locally Noetherian on its actual summand
open cover. No finite residual-index argument is required. -/
instance representedCMNormalCopies_locallyNoetherian :
    IsLocallyNoetherian (copies R U V) := by
  change IsLocallyNoetherian
    (∐ (fun _ : SmallCMResidualGroup D U V => (schemes R).obj V))
  apply (isLocallyNoetherian_iff_openCover
    (AlgebraicGeometry.sigmaOpenCover
      (fun _ : SmallCMResidualGroup D U V => (schemes R).obj V))).mpr
  intro g
  exact (R V).base.property.locallyNoetherian

/-- Each original graph is a closed immersion, so the identical original
comparison is locally of finite type by its summand open cover. -/
instance representedCMNormalKernelComparison_locallyOfFiniteType :
    LocallyOfFiniteType (kernelComparison R U V hVU) := by
  change LocallyOfFiniteType (Sigma.desc (graph R U V hVU))
  exact IsZariskiLocalAtSource.sigmaDesc (fun _ => by infer_instance)

/-- The original comparison is a monomorphism. The proof uses Hom injectivity
on its own locally Noetherian self-pullback, not an etaleness assumption. -/
theorem representedCMNormalKernelComparison_mono_of_dualGeometry
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) :
    Mono (kernelComparison R U V hVU) := by
  have hp : pullback.fst (kernelComparison R U V hVU) (kernelComparison R U V hVU) =
      pullback.snd (kernelComparison R U V hVU) (kernelComparison R U V hVU) := by
    apply representedCMNormalKernelComparison_locallyNoetherianHom_injective D C
      preservation composition unitCoherence associativity comparison symmetry
      stability square universality dualityNaturality polarizationStability
      compatibility h htor R U V hVU existence geometry hRigid
      (pullback (kernelComparison R U V hVU) (kernelComparison R U V hVU))
    exact pullback.condition
  refine ⟨fun {T} a b hab => ?_⟩
  calc
    a = pullback.lift a b hab ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
    _ = pullback.lift a b hab ≫ pullback.snd _ _ :=
      congrArg (fun f => pullback.lift a b hab ≫ f) hp
    _ = b := pullback.lift_snd _ _ _

/-- The explicit original comparison and the previously constructed original
section are inverse scheme morphisms under geometric coarse rigidity. -/
def representedCMNormalKernelSchemeIso
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) :
    copies R U V ≅ kernelPair R U V hVU := by
  have : Mono (kernelComparison R U V hVU) :=
    representedCMNormalKernelComparison_mono_of_dualGeometry D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry hRigid
  refine
    { hom := kernelComparison R U V hVU
      inv := kernelSection R U V hVU existence geometry
      hom_inv_id := ?_
      inv_hom_id := representedCMNormalKernelSection_comp D C preservation
        composition unitCoherence associativity comparison symmetry stability square
        universality dualityNaturality polarizationStability compatibility h htor
        R U V hVU existence geometry }
  apply (cancel_mono (kernelComparison R U V hVU)).mp
  rw [Category.assoc, representedCMNormalKernelSection_comp,
    Category.comp_id, Category.id_comp]

local notation "kernelIso" => representedCMNormalKernelSchemeIso D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

@[simp] theorem representedCMNormalKernelSchemeIso_hom
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) :
    (kernelIso R U V hVU existence geometry hRigid).hom =
      kernelComparison R U V hVU := rfl

@[simp] theorem representedCMNormalKernelSchemeIso_inv
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) :
    (kernelIso R U V hVU existence geometry hRigid).inv =
      kernelSection R U V hVU existence geometry := rfl

theorem representedCMNormalKernelComparison_isIso_of_dualGeometry
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) :
    IsIso (kernelComparison R U V hVU) := by
  change IsIso (kernelIso R U V hVU existence geometry hRigid).hom
  infer_instance

local notation "chosenReps" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "chosenComparison" => cmNormalKernelComparison D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU
local notation "chosenSection" => cmNormalKernelSection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

/-- The scheme isomorphism for precisely the witnesses defining cmSchemeTower,
with the direct original chosen comparison and previously constructed section. -/
def cmNormalKernelSchemeIso
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) :
    copies (chosenReps q) U V ≅ kernelPair (chosenReps q) U V hVU :=
  kernelIso (chosenReps q) U V hVU existence geometry hRigid

local notation "chosenIso" => cmNormalKernelSchemeIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU q

@[simp] theorem cmNormalKernelSchemeIso_hom
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) :
    (chosenIso existence geometry hRigid).hom = chosenComparison q := rfl

@[simp] theorem cmNormalKernelSchemeIso_inv
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) :
    (chosenIso existence geometry hRigid).inv = chosenSection q existence geometry := rfl

theorem cmNormalKernelComparison_mono_of_dualGeometry
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) :
    Mono (chosenComparison q) :=
  representedCMNormalKernelComparison_mono_of_dualGeometry D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry hRigid

theorem cmNormalKernelComparison_isIso_of_dualGeometry
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) :
    IsIso (chosenComparison q) :=
  representedCMNormalKernelComparison_isIso_of_dualGeometry D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry hRigid

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
