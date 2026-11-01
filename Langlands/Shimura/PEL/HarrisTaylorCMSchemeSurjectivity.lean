import Langlands.Shimura.PEL.HarrisTaylorCMLevelSurjectivity
import Langlands.Shimura.PEL.HarrisTaylorCMSchemeLevels
import Langlands.Shimura.PEL.HarrisTaylorCMBaseAdmissibility

/-! # Surjectivity of original represented CM transitions -/

noncomputable section

open CategoryTheory AlgebraicGeometry
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

private theorem map_surjective_of_naturalIso
    {J : Type*} [Category J] {P Q : J ⥤ Type 1} (e : P ≅ Q)
    {U V : J} (f : U ⟶ V) (hf : Function.Surjective (Q.map f)) :
    Function.Surjective (P.map f) := by
  intro y
  obtain ⟨x, hx⟩ := hf (e.hom.app V y)
  refine ⟨e.inv.app U x, ?_⟩
  calc
    P.map f (e.inv.app U x) = e.inv.app V (Q.map f x) :=
      (e.inv.naturality_apply f x).symm
    _ = e.inv.app V (e.hom.app V y) := congrArg (e.inv.app V) hx
    _ = y := (e.app V).toEquiv.left_inv y

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

/-- The unpointed tower has surjective original transporter maps at a field
spectrum, by evaluation at its identity geometric point. -/
theorem unpointed_identityPoint_map_surjective
    (hp : admissible (Over.mk p))
    {U V : HarrisLevel D} (f : U ⟶ V) :
    Function.Surjective ((untower ⟨Over.mk p, hp⟩).map f) := by
  let X : Bases := ⟨Over.mk p, hp⟩
  let a : HarrisGeometricPoint (Spec (CommRingCat.of Ω)) := ⟨Ω, 𝟙 _⟩
  let : ∀ k : GroupScheme.Tate.Index (fun _ => True),
      IsFinite (mu (Spec (CommRingCat.of Ω)) k.val).X.hom := hp.muFinite
  let : ∀ k : GroupScheme.Tate.Index (fun _ => True),
      Etale (mu (Spec (CommRingCat.of Ω)) k.val).X.hom := hp.muEtale
  apply map_surjective_of_naturalIso
    (unpointedClassTowerEvaluationIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor X a) f
  exact identityPoint_classMap_surjective D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality p compatibility
    h a.finiteFibers htor hp.torsionUnits hp.pairAdditivity f

include dualityNaturality polarizationStability in
/-- The disconnected presheaf retains the same surjectivity at every admitted
field spectrum, through its actual connected component inclusion. -/
theorem disconnected_identityPoint_map_surjective
    (hp : admissible (Over.mk p))
    (hd : ComponentwiseAdmissibleCMBase D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (Over.mk p))
    {U V : HarrisLevel D} (f : U ⟶ V) :
    Function.Surjective ((distower ⟨Over.mk p, hd⟩).map f) := by
  let X : DisBases := ⟨Over.mk p, hd⟩
  let c : _root_.ConnectedComponents (Spec (CommRingCat.of Ω)) :=
    .mk (Classical.arbitrary _)
  apply map_surjective_of_naturalIso
    (disconnectedClassTowerConnectedIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor X hp c) f
  exact unpointed_identityPoint_map_surjective D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor p hp f

end GeometricTest

/-- An actual field test scheme is admitted using the two
named relative dual assertions. No test-category membership is assumed. -/
def cmGeometricTestBase
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] (p : Spec (CommRingCat.of Ω) ⟶ Spec (.of F)) :
    DisBases := by
  letI : IsLocallyNoetherian (Over.mk p).left :=
    show IsLocallyNoetherian (Spec (CommRingCat.of Ω)) from inferInstance
  exact ⟨Over.mk p, componentwiseAdmissibleCMBase_of_relativeDual D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality existence geometry (Over.mk p)⟩

local notation "testBase" => cmGeometricTestBase D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality

include dualityNaturality polarizationStability in
/-- The actual disconnected class presheaf has surjective transporter maps at
every algebraically closed field test scheme obtained from named dual geometry. -/
theorem cmGeometricTestBase_map_surjective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (p : Spec (CommRingCat.of Ω) ⟶ Spec (.of F))
    {U V : HarrisLevel D} (f : U ⟶ V) :
    Function.Surjective ((distower (testBase existence geometry p)).map f) := by
  let : IsLocallyNoetherian (Over.mk p).left :=
    show IsLocallyNoetherian (Spec (CommRingCat.of Ω)) from inferInstance
  let : ConnectedSpace (Over.mk p).left :=
    show ConnectedSpace (Spec (CommRingCat.of Ω)) from inferInstance
  have hp : admissible (Over.mk p) :=
    (admissibleCMBase_iff_dualGeometry D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (Over.mk p)).mpr
        (fun B => ⟨existence _ B, geometry _ B (existence _ B)⟩)
  exact disconnected_identityPoint_map_surjective D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor p hp
    (testBase existence geometry p).property f

local notation "moduli" => smallLevelClassPresheafTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "baseTower" => representedCMBaseTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "schemeTower" => representedCMSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

variable (R : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)

/-- Each original represented transition lifts every actual geometric-field
map, by its exact interpretation of the same CM classes. -/
theorem representedCMGeometricHom_map_surjective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (p : Spec (CommRingCat.of Ω) ⟶ Spec (.of F))
    {U V : SmallCMLevel D} (k : U ⟶ V) :
    Function.Surjective (fun f : testBase existence geometry p ⟶ (R U).base =>
      f ≫ (baseTower R).map k) := by
  let S : DisBases := testBase existence geometry p
  intro f
  let q := (R V).represents.hom.app (Opposite.op S) (ULift.up f)
  obtain ⟨qU, hq⟩ := cmGeometricTestBase_map_surjective D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor existence geometry p k.hom q
  let fU : S ⟶ (R U).base :=
    ((R U).represents.inv.app (Opposite.op S) qU).down
  refine ⟨fU, ?_⟩
  apply ULift.up_injective
  apply ((R V).represents.app (Opposite.op S)).toEquiv.injective
  change (R V).represents.hom.app (Opposite.op S)
      (ULift.up (fU ≫ (baseTower R).map k)) = q
  rw [representedCMBaseTower_map_classes D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor R k S fU]
  have hu : (R U).represents.hom.app (Opposite.op S) (ULift.up fU) = qU :=
    ((R U).represents.app (Opposite.op S)).toEquiv.apply_symm_apply qU
  rw [hu]
  exact hq

/-- A chosen actual geometric-field lift through an original represented
transition. The map is obtained from proved class surjectivity and the exact
representing isomorphisms. -/
def representedCMGeometricPointLift
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {U V : SmallCMLevel D} (k : U ⟶ V)
    (a : Spec (CommRingCat.of Ω) ⟶ (schemeTower R).obj V) :
    Spec (CommRingCat.of Ω) ⟶ (schemeTower R).obj U := by
  let p := a ≫ (R V).base.obj.hom
  let f : testBase existence geometry p ⟶ (R V).base :=
    ObjectProperty.homMk (Over.homMk a rfl)
  exact (Function.surjInv (representedCMGeometricHom_map_surjective D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor R
    existence geometry p k) f).hom.left

local notation "liftPoint" => representedCMGeometricPointLift D C preservation
  composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor

/-- The constructed lift lies above the specified original geometric point. -/
@[reassoc (attr := simp)]
theorem representedCMGeometricPointLift_comp
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {U V : SmallCMLevel D} (k : U ⟶ V)
    (a : Spec (CommRingCat.of Ω) ⟶ (schemeTower R).obj V) :
    liftPoint R existence geometry k a ≫ (schemeTower R).map k = a := by
  let p := a ≫ (R V).base.obj.hom
  let f : testBase existence geometry p ⟶ (R V).base :=
    ObjectProperty.homMk (Over.homMk a rfl)
  exact congrArg
    (fun b : testBase existence geometry p ⟶ (R V).base => b.hom.left)
    (Function.surjInv_eq (representedCMGeometricHom_map_surjective D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor R
      existence geometry p k) f)

/-- Every original represented transporter is surjective on actual scheme
points. Algebraic closures of residue fields supply enough geometric tests. -/
theorem representedCMSchemeTower_map_surjective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {U V : SmallCMLevel D} (k : U ⟶ V) :
    Function.Surjective ((schemeTower R).map k) := by
  intro y
  let a := HarrisGeometricPoint.ofResidue ((schemeTower R).obj V) y
  let x : Spec (CommRingCat.of a.Ω) := Classical.arbitrary _
  refine ⟨liftPoint R existence geometry k a.hom x, ?_⟩
  calc
    (schemeTower R).map k (liftPoint R existence geometry k a.hom x) =
        a.hom x := congrArg
      (fun b : Spec (CommRingCat.of a.Ω) ⟶ (schemeTower R).obj V => b x)
      (representedCMGeometricPointLift_comp D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor R existence geometry k a.hom)
    _ = y := by
      change ((schemeTower R).obj V).fromSpecResidueField y _ = y
      exact Scheme.fromSpecResidueField_apply _ _

/-- Specialization to the exact previously stated CM representability target,
using the same chosen representations that define `cmSchemeTower`. -/
theorem cmSchemeTower_map_surjective
    (q : CMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {U V : SmallCMLevel D} (k : U ⟶ V) :
    Function.Surjective ((cmSchemeTower D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q).map k) :=
  representedCMSchemeTower_map_surjective D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor
    (chosenCMLevelRepresentation D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q) existence geometry k

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
