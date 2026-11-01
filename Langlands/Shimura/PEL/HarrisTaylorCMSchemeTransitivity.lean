import Langlands.Shimura.PEL.HarrisTaylorCMClassTransitivity
import Langlands.Shimura.PEL.HarrisTaylorCMSchemeSurjectivity
import Langlands.Shimura.PEL.HarrisTaylorCMNormalRefinement

/-! # Residual translation in original represented CM fibers -/

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

section GeometricTest

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]
  (p : Spec (CommRingCat.of Ω) ⟶ Spec (.of F))
  (U V : HarrisLevel D) (hVU : V.subgroup ≤ U.subgroup)
  [(V.subgroup.subgroupOf U.subgroup).Normal]

/-- Evaluation at the identity geometric point transfers the original
class-fiber translation theorem to the same unpointed tower. -/
theorem unpointed_identityPoint_exists_normalTranslate
    (hp : admissible (Over.mk p))
    (x y : (untower ⟨Over.mk p, hp⟩).obj V)
    (hxy : (untower ⟨Over.mk p, hp⟩).map (CompactOpenLevel.inclusion hVU) x =
      (untower ⟨Over.mk p, hp⟩).map (CompactOpenLevel.inclusion hVU) y) :
    ∃ g : U.subgroup,
      (untower ⟨Over.mk p, hp⟩).map
        (CompactOpenLevel.normalInverseArrow U V hVU g) x = y := by
  let X : Bases := ⟨Over.mk p, hp⟩
  let a : HarrisGeometricPoint (Spec (CommRingCat.of Ω)) := ⟨Ω, 𝟙 _⟩
  let : ∀ k : GroupScheme.Tate.Index (fun _ => True),
      IsFinite (mu (Spec (CommRingCat.of Ω)) k.val).X.hom := hp.muFinite
  let : ∀ k : GroupScheme.Tate.Index (fun _ => True),
      Etale (mu (Spec (CommRingCat.of Ω)) k.val).X.hom := hp.muEtale
  apply exists_translate_of_naturalIso
    (unpointedClassTowerEvaluationIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor X a) (CompactOpenLevel.inclusion hVU)
    (CompactOpenLevel.normalInverseArrow U V hVU) _ x y hxy
  intro q r hqr
  exact classMap_exists_normalTranslate D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality p compatibility
    h a.hom a.finiteFibers htor hp.torsionUnits hp.pairAdditivity U V hVU q r hqr

include dualityNaturality polarizationStability in
/-- Actual connected-component inclusion transfers translation existence to
Harris's disconnected product presheaf on a geometric field test. -/
theorem disconnected_identityPoint_exists_normalTranslate
    (hp : admissible (Over.mk p))
    (hd : ComponentwiseAdmissibleCMBase D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (Over.mk p))
    (x y : (distower ⟨Over.mk p, hd⟩).obj V)
    (hxy : (distower ⟨Over.mk p, hd⟩).map (CompactOpenLevel.inclusion hVU) x =
      (distower ⟨Over.mk p, hd⟩).map (CompactOpenLevel.inclusion hVU) y) :
    ∃ g : U.subgroup,
      (distower ⟨Over.mk p, hd⟩).map
        (CompactOpenLevel.normalInverseArrow U V hVU g) x = y := by
  let X : DisBases := ⟨Over.mk p, hd⟩
  let c : _root_.ConnectedComponents (Spec (CommRingCat.of Ω)) :=
    .mk (Classical.arbitrary _)
  apply exists_translate_of_naturalIso
    (disconnectedClassTowerConnectedIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor X hp c)
    (CompactOpenLevel.inclusion hVU) (CompactOpenLevel.normalInverseArrow U V hVU)
    _ x y hxy
  exact unpointed_identityPoint_exists_normalTranslate D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor p U V hVU hp

end GeometricTest

local notation "testBase" => cmGeometricTestBase D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality

include dualityNaturality polarizationStability in
/-- Named relative dual geometry admits the actual field spectrum and supplies
translation existence for its original disconnected class map. -/
theorem cmGeometricTestBase_exists_normalTranslate
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (p : Spec (CommRingCat.of Ω) ⟶ Spec (.of F))
    (U V : HarrisLevel D) (hVU : V.subgroup ≤ U.subgroup)
    [(V.subgroup.subgroupOf U.subgroup).Normal]
    (x y : (distower (testBase existence geometry p)).obj V)
    (hxy : (distower (testBase existence geometry p)).map
        (CompactOpenLevel.inclusion hVU) x =
      (distower (testBase existence geometry p)).map
        (CompactOpenLevel.inclusion hVU) y) :
    ∃ g : U.subgroup,
      (distower (testBase existence geometry p)).map
        (CompactOpenLevel.normalInverseArrow U V hVU g) x = y := by
  let : IsLocallyNoetherian (Over.mk p).left :=
    show IsLocallyNoetherian (Spec (CommRingCat.of Ω)) from inferInstance
  let : ConnectedSpace (Over.mk p).left :=
    show ConnectedSpace (Spec (CommRingCat.of Ω)) from inferInstance
  have hp : admissible (Over.mk p) :=
    (admissibleCMBase_iff_dualGeometry D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (Over.mk p)).mpr
        (fun B => ⟨existence _ B, geometry _ B (existence _ B)⟩)
  exact disconnected_identityPoint_exists_normalTranslate D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor p U V hVU hp
    (testBase existence geometry p).property x y hxy

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

/-- Equal coarse geometric-test morphisms differ by an original subgroup
translation, using the exact representing isomorphisms. -/
theorem representedCMGeometricHom_exists_normalTranslate
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (p : Spec (CommRingCat.of Ω) ⟶ Spec (.of F))
    (x y : testBase existence geometry p ⟶ (R V).base)
    (hxy : x ≫ (baseTower R).map (smallCMInclusion D hVU) =
      y ≫ (baseTower R).map (smallCMInclusion D hVU)) :
    ∃ g : U.obj.subgroup,
      x ≫ (baseAction R U V hVU).ρ (QuotientGroup.mk g) = y := by
  let S : DisBases := testBase existence geometry p
  let qx : (distower S).obj V.obj :=
    (R V).represents.hom.app (Opposite.op S) (ULift.up x)
  let qy : (distower S).obj V.obj :=
    (R V).represents.hom.app (Opposite.op S) (ULift.up y)
  have hc : (distower S).map (CompactOpenLevel.inclusion hVU) qx =
      (distower S).map (CompactOpenLevel.inclusion hVU) qy := by
    change ((moduli).map (smallCMInclusion D hVU)).app (Opposite.op S) qx =
      ((moduli).map (smallCMInclusion D hVU)).app (Opposite.op S) qy
    dsimp only [qx, qy]
    rw [← representedCMBaseTower_map_classes D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R (smallCMInclusion D hVU) S x,
      ← representedCMBaseTower_map_classes D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R (smallCMInclusion D hVU) S y, hxy]
  obtain ⟨g, hg⟩ := cmGeometricTestBase_exists_normalTranslate D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    existence geometry p U.obj V.obj hVU qx qy hc
  refine ⟨g, ?_⟩
  apply ULift.up_injective
  apply ((R V).represents.app (Opposite.op S)).toEquiv.injective
  change (R V).represents.hom.app (Opposite.op S)
    (ULift.up (x ≫ (baseAction R U V hVU).ρ (QuotientGroup.mk g))) = qy
  rw [representedCMNormalQuotientBaseAction_mk_classes D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor R U V hVU g S x]
  exact hg

/-- Two actual geometric-field maps in one original forgetting fiber differ
by the existing residual quotient action. -/
theorem representedCMGeometricPoint_exists_normalTranslate
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (a b : Spec (CommRingCat.of Ω) ⟶ (schemes R).obj V)
    (hab : a ≫ projection R U V hVU = b ≫ projection R U V hVU) :
    ∃ g : SmallCMResidualGroup D U V, a ≫ (quotientAction R U V hVU).ρ g = b := by
  let p := a ≫ (R V).base.obj.hom
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
  let x : testBase existence geometry p ⟶ (R V).base :=
    ObjectProperty.homMk (Over.homMk a rfl)
  let y : testBase existence geometry p ⟶ (R V).base :=
    ObjectProperty.homMk (Over.homMk b hb)
  have hxy : x ≫ (baseTower R).map (smallCMInclusion D hVU) =
      y ≫ (baseTower R).map (smallCMInclusion D hVU) := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hab
  obtain ⟨g, hg⟩ := representedCMGeometricHom_exists_normalTranslate D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    R U V hVU existence geometry p x y hxy
  exact ⟨QuotientGroup.mk g,
    congrArg (fun f : testBase existence geometry p ⟶ (R V).base => f.hom.left) hg⟩

/-- Choose a residual translation between two specified actual maps in one
coarse fiber, using the proved existence theorem. -/
def representedCMGeometricTranslation
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (a b : Spec (CommRingCat.of Ω) ⟶ (schemes R).obj V)
    (hab : a ≫ projection R U V hVU = b ≫ projection R U V hVU) :
    SmallCMResidualGroup D U V :=
  Classical.choose (representedCMGeometricPoint_exists_normalTranslate D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    R U V hVU existence geometry a b hab)

/-- The chosen translation acts by the exact original residual action. -/
theorem representedCMGeometricTranslation_action
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (a b : Spec (CommRingCat.of Ω) ⟶ (schemes R).obj V)
    (hab : a ≫ projection R U V hVU = b ≫ projection R U V hVU) :
    a ≫ (quotientAction R U V hVU).ρ
      (representedCMGeometricTranslation D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor R U V hVU existence geometry a b hab) =
      b :=
  Classical.choose_spec (representedCMGeometricPoint_exists_normalTranslate D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    R U V hVU existence geometry a b hab)

local notation "chosenReps" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "chosenSchemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "chosenAction" => cmNormalQuotientAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

/-- The exact chosen representations defining `cmSchemeTower` have transitive
geometric fibers for the existing normal residual action. -/
theorem cmGeometricPoint_exists_normalTranslate
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (a b : Spec (CommRingCat.of Ω) ⟶ (chosenSchemes q).obj V)
    (hab : a ≫ (chosenSchemes q).map (smallCMInclusion D hVU) =
      b ≫ (chosenSchemes q).map (smallCMInclusion D hVU)) :
    ∃ g : SmallCMResidualGroup D U V, a ≫ (chosenAction q).ρ g = b :=
  representedCMGeometricPoint_exists_normalTranslate D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry a b hab

/-- Specialize the chosen residual translation to the identical chosen CM tower. -/
def cmGeometricTranslation
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (a b : Spec (CommRingCat.of Ω) ⟶ (chosenSchemes q).obj V)
    (hab : a ≫ (chosenSchemes q).map (smallCMInclusion D hVU) =
      b ≫ (chosenSchemes q).map (smallCMInclusion D hVU)) :
    SmallCMResidualGroup D U V :=
  representedCMGeometricTranslation D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor (chosenReps q) U V hVU
    existence geometry a b hab

/-- The specialized choice has the same actual action equation on `cmSchemeTower`. -/
theorem cmGeometricTranslation_action
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (a b : Spec (CommRingCat.of Ω) ⟶ (chosenSchemes q).obj V)
    (hab : a ≫ (chosenSchemes q).map (smallCMInclusion D hVU) =
      b ≫ (chosenSchemes q).map (smallCMInclusion D hVU)) :
    a ≫ (chosenAction q).ρ
      (cmGeometricTranslation D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor U V hVU q existence geometry a b hab) =
      b :=
  representedCMGeometricTranslation_action D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor (chosenReps q) U V hVU
    existence geometry a b hab

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
