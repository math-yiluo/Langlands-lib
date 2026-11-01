import Langlands.Shimura.PEL.HarrisTaylorCMSchemeTransitivity
import Langlands.Shimura.PEL.HarrisTaylorCMNormalKernelPair

/-! # Original CM kernel lifts on connected scheme tests -/

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

local notation "DisBases" => ComponentwiseAdmissibleCMBaseCategory D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality

private theorem exists_translate_of_naturalIso
    {J : Type*} [Category J] {P Q : J ⥤ Type 1} (e : P ≅ Q)
    {U V : J} (f : V ⟶ U) {G : Type*} (a : G → (V ⟶ V))
    (ht : ∀ x y : Q.obj V, Q.map f x = Q.map f y →
      ∃ g, Q.map (a g) x = y)
    (x y : P.obj V) (hxy : P.map f x = P.map f y) :
    ∃ g, P.map (a g) x = y := by
  have hc : Q.map f (e.hom.app V x) = Q.map f (e.hom.app V y) := by
    rw [← e.hom.naturality_apply, ← e.hom.naturality_apply, hxy]
  obtain ⟨g, hg⟩ := ht (e.hom.app V x) (e.hom.app V y) hc
  refine ⟨g, (e.app V).toEquiv.injective ?_⟩
  exact (e.hom.naturality_apply (a g) x).trans hg

local notation "Bases" => AdmissibleCMBaseCategory D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "admissible" => AdmissibleCMBase D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "untower" => unpointedClassTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor
local notation "distower" => disconnectedClassTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor

/-- Original fine class fibers are transitive on every connected admissible
scheme test, including nonreduced schemes. -/
theorem unpointed_exists_normalTranslate
    (X : Bases) (U V : HarrisLevel D) (hVU : V.subgroup ≤ U.subgroup)
    [(V.subgroup.subgroupOf U.subgroup).Normal]
    (x y : (untower X).obj V)
    (hxy : (untower X).map (CompactOpenLevel.inclusion hVU) x =
      (untower X).map (CompactOpenLevel.inclusion hVU) y) :
    ∃ g : U.subgroup,
      (untower X).map (CompactOpenLevel.normalInverseArrow U V hVU g) x = y := by
  let a := HarrisGeometricPoint.ofResidue X.obj.left (Classical.arbitrary _)
  apply exists_translate_of_naturalIso
    (unpointedClassTowerEvaluationIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor X a) (CompactOpenLevel.inclusion hVU)
    (CompactOpenLevel.normalInverseArrow U V hVU) _ x y hxy
  intro q r hqr
  exact classMap_exists_normalTranslate D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality X.obj.hom
    compatibility h a.hom a.finiteFibers htor X.property.torsionUnits
    X.property.pairAdditivity U V hVU q r hqr

include dualityNaturality polarizationStability in
/-- On a connected admissible scheme, the original disconnected product
has the same transitive fine class fibers. -/
theorem disconnected_connected_exists_normalTranslate
    (X : DisBases) (hX : admissible X.obj)
    (U V : HarrisLevel D) (hVU : V.subgroup ≤ U.subgroup)
    [(V.subgroup.subgroupOf U.subgroup).Normal]
    (x y : (distower X).obj V)
    (hxy : (distower X).map (CompactOpenLevel.inclusion hVU) x =
      (distower X).map (CompactOpenLevel.inclusion hVU) y) :
    ∃ g : U.subgroup,
      (distower X).map (CompactOpenLevel.normalInverseArrow U V hVU g) x = y := by
  let : ConnectedSpace X.obj.left := hX.connected
  let c : _root_.ConnectedComponents X.obj.left :=
    .mk (Classical.arbitrary _)
  apply exists_translate_of_naturalIso
    (disconnectedClassTowerConnectedIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor X hX c)
    (CompactOpenLevel.inclusion hVU) (CompactOpenLevel.normalInverseArrow U V hVU)
    _ x y hxy
  exact unpointed_exists_normalTranslate D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality
    compatibility h htor ⟨X.obj, hX⟩ U V hVU

local notation "moduli" => smallLevelClassPresheafTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "baseTower" => representedCMBaseTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "schemes" => representedCMSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "baseAction" => representedCMNormalQuotientBaseAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
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

/-- The representing isomorphisms transfer transitivity on a connected
admissible scheme to equality of actual over-category morphisms. -/
theorem representedCMConnectedHom_exists_normalTranslate
    (X : DisBases) (hX : admissible X.obj)
    (x y : X ⟶ (R V).base)
    (hxy : x ≫ (baseTower R).map (smallCMInclusion D hVU) =
      y ≫ (baseTower R).map (smallCMInclusion D hVU)) :
    ∃ g : U.obj.subgroup,
      x ≫ (baseAction R U V hVU).ρ (QuotientGroup.mk g) = y := by
  let qx : (distower X).obj V.obj :=
    (R V).represents.hom.app (Opposite.op X) (ULift.up x)
  let qy : (distower X).obj V.obj :=
    (R V).represents.hom.app (Opposite.op X) (ULift.up y)
  have hc : (distower X).map (CompactOpenLevel.inclusion hVU) qx =
      (distower X).map (CompactOpenLevel.inclusion hVU) qy := by
    change ((moduli).map (smallCMInclusion D hVU)).app (Opposite.op X) qx =
      ((moduli).map (smallCMInclusion D hVU)).app (Opposite.op X) qy
    dsimp only [qx, qy]
    rw [← representedCMBaseTower_map_classes D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R (smallCMInclusion D hVU) X x,
      ← representedCMBaseTower_map_classes D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R (smallCMInclusion D hVU) X y, hxy]
  obtain ⟨g, hg⟩ := disconnected_connected_exists_normalTranslate D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    X hX U.obj V.obj hVU qx qy hc
  refine ⟨g, ?_⟩
  apply ULift.up_injective
  apply ((R V).represents.app (Opposite.op X)).toEquiv.injective
  change (R V).represents.hom.app (Opposite.op X)
    (ULift.up (x ≫ (baseAction R U V hVU).ρ (QuotientGroup.mk g))) = qy
  rw [representedCMNormalQuotientBaseAction_mk_classes D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor R U V hVU g X x]
  exact hg

/-- Two maps from any connected locally Noetherian scheme in the same
original forgetting fiber differ by an original residual map. -/
theorem representedCMConnectedMap_exists_normalTranslate
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {T : Scheme.{0}} [ConnectedSpace T] [IsLocallyNoetherian T]
    (a b : T ⟶ (schemes R).obj V)
    (hab : a ≫ projection R U V hVU = b ≫ projection R U V hVU) :
    ∃ g : SmallCMResidualGroup D U V, a ≫ (quotientAction R U V hVU).ρ g = b := by
  let p := a ≫ (R V).base.obj.hom
  let : ConnectedSpace (Over.mk p).left := show ConnectedSpace T from inferInstance
  let : IsLocallyNoetherian (Over.mk p).left :=
    show IsLocallyNoetherian T from inferInstance
  have hp : admissible (Over.mk p) :=
    (admissibleCMBase_iff_dualGeometry D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (Over.mk p)).mpr
        (fun B => ⟨existence _ B, geometry _ B (existence _ B)⟩)
  let X : DisBases := ⟨Over.mk p,
    componentwiseAdmissibleCMBase_of_relativeDual D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      existence geometry (Over.mk p)⟩
  have hb : b ≫ (R V).base.obj.hom = p := by
    have he : projection R U V hVU ≫ (R U).base.obj.hom =
        (R V).base.obj.hom :=
      representedCMSchemeTower_over D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor R (smallCMInclusion D hVU)
    calc
      b ≫ (R V).base.obj.hom =
          (b ≫ projection R U V hVU) ≫ (R U).base.obj.hom := by
        rw [Category.assoc, he]
      _ = (a ≫ projection R U V hVU) ≫ (R U).base.obj.hom :=
        congrArg (fun f => f ≫ (R U).base.obj.hom) hab.symm
      _ = p := by rw [Category.assoc, he]
  let x : X ⟶ (R V).base := ObjectProperty.homMk (Over.homMk a rfl)
  let y : X ⟶ (R V).base := ObjectProperty.homMk (Over.homMk b hb)
  have hxy : x ≫ (baseTower R).map (smallCMInclusion D hVU) =
      y ≫ (baseTower R).map (smallCMInclusion D hVU) := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hab
  obtain ⟨g, hg⟩ := representedCMConnectedHom_exists_normalTranslate D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    R U V hVU X hp x y hxy
  exact ⟨QuotientGroup.mk g,
    congrArg (fun f : X ⟶ (R V).base => f.hom.left) hg⟩

local notation "copies" => representedCMNormalCopies D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "kernelPair" => representedCMNormalKernelPair D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "kernelComparison" => representedCMNormalKernelComparison D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- Choose the translating original residual element for a connected scheme
map into the exact original kernel pair. -/
def representedCMNormalKernelConnectedTranslation
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {T : Scheme.{0}} [ConnectedSpace T] [IsLocallyNoetherian T]
    (c : T ⟶ kernelPair R U V hVU) : SmallCMResidualGroup D U V :=
  Classical.choose (representedCMConnectedMap_exists_normalTranslate D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    R U V hVU existence geometry (c ≫ pullback.fst _ _) (c ≫ pullback.snd _ _)
    (by simp only [Category.assoc, pullback.condition]))

local notation "translation" => representedCMNormalKernelConnectedTranslation D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

theorem representedCMNormalKernelConnectedTranslation_action
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {T : Scheme.{0}} [ConnectedSpace T] [IsLocallyNoetherian T]
    (c : T ⟶ kernelPair R U V hVU) :
    (c ≫ pullback.fst _ _) ≫ (quotientAction R U V hVU).ρ
        (translation R U V hVU existence geometry c) = c ≫ pullback.snd _ _ :=
  Classical.choose_spec (representedCMConnectedMap_exists_normalTranslate D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    R U V hVU existence geometry (c ≫ pullback.fst _ _) (c ≫ pullback.snd _ _)
    (by simp only [Category.assoc, pullback.condition]))

/-- An actual scheme morphism lifting every connected locally Noetherian
test into an original residual summand. -/
def representedCMNormalKernelConnectedLift
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {T : Scheme.{0}} [ConnectedSpace T] [IsLocallyNoetherian T]
    (c : T ⟶ kernelPair R U V hVU) : T ⟶ copies R U V :=
  (c ≫ pullback.fst (projection R U V hVU) (projection R U V hVU)) ≫
    Sigma.ι (fun _ : SmallCMResidualGroup D U V => (schemes R).obj V)
      (translation R U V hVU existence geometry c)

local notation "liftKernel" => representedCMNormalKernelConnectedLift D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- The constructed lift composes with the identical original comparison. -/
@[reassoc (attr := simp)] theorem representedCMNormalKernelConnectedLift_comp
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {T : Scheme.{0}} [ConnectedSpace T] [IsLocallyNoetherian T]
    (c : T ⟶ kernelPair R U V hVU) :
    liftKernel R U V hVU existence geometry c ≫ kernelComparison R U V hVU = c := by
  apply pullback.hom_ext
  · simp only [representedCMNormalKernelConnectedLift, Category.assoc,
      representedCMNormalKernelComparison_ι_assoc, representedCMNormalGraph_fst,
      Category.comp_id]
  · simp only [representedCMNormalKernelConnectedLift, Category.assoc,
      representedCMNormalKernelComparison_ι_assoc, representedCMNormalGraph_snd]
    exact representedCMNormalKernelConnectedTranslation_action D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry c

/-- Postcomposition with the original comparison is surjective on actual
scheme Hom sets for all connected locally Noetherian sources. -/
theorem representedCMNormalKernelComparison_connectedHom_surjective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (T : Scheme.{0}) [ConnectedSpace T] [IsLocallyNoetherian T] :
    Function.Surjective
      (fun d : T ⟶ copies R U V => d ≫ kernelComparison R U V hVU) := by
  intro c
  exact ⟨liftKernel R U V hVU existence geometry c,
    representedCMNormalKernelConnectedLift_comp D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor R U V hVU
      existence geometry c⟩

local notation "chosenReps" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "chosenSchemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "chosenAction" => cmNormalQuotientAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU
local notation "chosenComparison" => cmNormalKernelComparison D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

/-- Transitivity for actual maps into the identical chosen CM tower. -/
theorem cmConnectedMap_exists_normalTranslate
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {T : Scheme.{0}} [ConnectedSpace T] [IsLocallyNoetherian T]
    (a b : T ⟶ (chosenSchemes q).obj V)
    (hab : a ≫ (chosenSchemes q).map (smallCMInclusion D hVU) =
      b ≫ (chosenSchemes q).map (smallCMInclusion D hVU)) :
    ∃ g : SmallCMResidualGroup D U V, a ≫ (chosenAction q).ρ g = b :=
  representedCMConnectedMap_exists_normalTranslate D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry a b hab

/-- The connected-scheme lift for exactly the witnesses defining cmSchemeTower. -/
def cmNormalKernelConnectedLift
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {T : Scheme.{0}} [ConnectedSpace T] [IsLocallyNoetherian T]
    (c : T ⟶ kernelPair (chosenReps q) U V hVU) :
    T ⟶ copies (chosenReps q) U V :=
  liftKernel (chosenReps q) U V hVU existence geometry c

local notation "chosenLift" => cmNormalKernelConnectedLift D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU q

/-- The chosen lift is literally the first projection into the original
summand indexed by the constructed translation. -/
theorem cmNormalKernelConnectedLift_eq
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {T : Scheme.{0}} [ConnectedSpace T] [IsLocallyNoetherian T]
    (c : T ⟶ kernelPair (chosenReps q) U V hVU) :
    chosenLift existence geometry c =
      (c ≫ pullback.fst ((chosenSchemes q).map (smallCMInclusion D hVU))
        ((chosenSchemes q).map (smallCMInclusion D hVU))) ≫
      Sigma.ι (fun _ : SmallCMResidualGroup D U V => (chosenSchemes q).obj V)
        (translation (chosenReps q) U V hVU existence geometry c) := rfl

@[reassoc (attr := simp)] theorem cmNormalKernelConnectedLift_comp
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {T : Scheme.{0}} [ConnectedSpace T] [IsLocallyNoetherian T]
    (c : T ⟶ kernelPair (chosenReps q) U V hVU) :
    chosenLift existence geometry c ≫ chosenComparison q = c :=
  representedCMNormalKernelConnectedLift_comp D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry c

/-- The exact chosen comparison is surjective on scheme Hom sets for every
connected locally Noetherian source. -/
theorem cmNormalKernelComparison_connectedHom_surjective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (T : Scheme.{0}) [ConnectedSpace T] [IsLocallyNoetherian T] :
    Function.Surjective
      (fun d : T ⟶ copies (chosenReps q) U V => d ≫ chosenComparison q) :=
  representedCMNormalKernelComparison_connectedHom_surjective D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry T

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
