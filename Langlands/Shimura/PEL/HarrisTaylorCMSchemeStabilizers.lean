import Langlands.Shimura.PEL.HarrisTaylorCMClassStabilizers
import Langlands.Shimura.PEL.HarrisTaylorCMSchemeTransitivity

/-! # Geometric freeness of the original represented CM residual action -/

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

local notation "Bases" => AdmissibleCMBaseCategory D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "DisBases" => ComponentwiseAdmissibleCMBaseCategory D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
local notation "admissible" => AdmissibleCMBase D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "untower" => unpointedClassTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor
local notation "distower" => disconnectedClassTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor

/-- Actual coarse-level rigidity at every admitted algebraically closed field
spectrum, using its identity geometric point and the same representative tests.
This property is not inferred from sufficiently small level. -/
def CMGeometricCoarseRigidity (U : HarrisLevel D) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (p : Spec (CommRingCat.of Ω) ⟶ Spec (.of F))
    (hp : admissible (Over.mk p)),
    letI : ∀ k : GroupScheme.Tate.Index (fun _ => True),
        IsFinite (mu (Spec (CommRingCat.of Ω)) k.val).X.hom := hp.muFinite
    letI : ∀ k : GroupScheme.Tate.Index (fun _ => True),
        Etale (mu (Spec (CommRingCat.of Ω)) k.val).X.hom := hp.muEtale
    CoarseLevelHasNoAutomorphisms D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality p compatibility
      h (𝟙 _) (HarrisGeometricPoint.mk Ω (𝟙 _)).finiteFibers htor hp.torsionUnits
      hp.pairAdditivity U

local notation "Rigid" => CMGeometricCoarseRigidity D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor

private theorem translate_eq_iff_of_naturalIso
    {J : Type*} [Category J] {P Q : J ⥤ Type 1} (e : P ≅ Q)
    {V : J} (a b : V ⟶ V) (R : Prop)
    (ht : ∀ x : Q.obj V, Q.map a x = Q.map b x ↔ R) (x : P.obj V) :
    P.map a x = P.map b x ↔ R := by
  constructor
  · intro hx
    apply (ht (e.hom.app V x)).mp
    rw [← e.hom.naturality_apply, ← e.hom.naturality_apply, hx]
  · intro hr
    apply (e.app V).toEquiv.injective
    change e.hom.app V (P.map a x) = e.hom.app V (P.map b x)
    rw [e.hom.naturality_apply, e.hom.naturality_apply]
    exact (ht (e.hom.app V x)).mpr hr

section GeometricTest

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]
  (p : Spec (CommRingCat.of Ω) ⟶ Spec (.of F))
  (U V : HarrisLevel D) (hVU : V.subgroup ≤ U.subgroup)
  [(V.subgroup.subgroupOf U.subgroup).Normal]

/-- Evaluation at the actual identity point transfers the exact original
class stabilizer criterion to the unpointed CM level tower. -/
theorem unpointed_identityPoint_normalTranslate_eq_iff
    (hRigid : Rigid U) (hp : admissible (Over.mk p))
    (g k : U.subgroup) (x : (untower ⟨Over.mk p, hp⟩).obj V) :
    (untower ⟨Over.mk p, hp⟩).map
        (CompactOpenLevel.normalInverseArrow U V hVU g) x =
      (untower ⟨Over.mk p, hp⟩).map
        (CompactOpenLevel.normalInverseArrow U V hVU k) x ↔
      (g : U.subgroup ⧸ V.subgroup.subgroupOf U.subgroup) = k := by
  let X : Bases := ⟨Over.mk p, hp⟩
  let a : HarrisGeometricPoint (Spec (CommRingCat.of Ω)) := ⟨Ω, 𝟙 _⟩
  let : ∀ j : GroupScheme.Tate.Index (fun _ => True),
      IsFinite (mu (Spec (CommRingCat.of Ω)) j.val).X.hom := hp.muFinite
  let : ∀ j : GroupScheme.Tate.Index (fun _ => True),
      Etale (mu (Spec (CommRingCat.of Ω)) j.val).X.hom := hp.muEtale
  apply translate_eq_iff_of_naturalIso
    (unpointedClassTowerEvaluationIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor X a)
    (CompactOpenLevel.normalInverseArrow U V hVU g)
    (CompactOpenLevel.normalInverseArrow U V hVU k) _ _ x
  intro q
  refine (classMap_normalTranslate_eq_iff D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality p compatibility
    h a.hom a.finiteFibers htor hp.torsionUnits hp.pairAdditivity U V hVU
    (hRigid Ω p hp) g k q).trans ?_
  constructor
  · intro hm
    exact QuotientGroup.eq_iff_div_mem.mpr hm
  · intro he
    have hm := QuotientGroup.eq_iff_div_mem.mp he
    exact hm

include dualityNaturality polarizationStability in
/-- The actual connected-component inclusion transfers the exact equality
criterion to Harris's disconnected product presheaf on a geometric test. -/
theorem disconnected_identityPoint_normalTranslate_eq_iff
    (hRigid : Rigid U) (hp : admissible (Over.mk p))
    (hd : ComponentwiseAdmissibleCMBase D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (Over.mk p))
    (g k : U.subgroup) (x : (distower ⟨Over.mk p, hd⟩).obj V) :
    (distower ⟨Over.mk p, hd⟩).map
        (CompactOpenLevel.normalInverseArrow U V hVU g) x =
      (distower ⟨Over.mk p, hd⟩).map
        (CompactOpenLevel.normalInverseArrow U V hVU k) x ↔
      (g : U.subgroup ⧸ V.subgroup.subgroupOf U.subgroup) = k := by
  let X : DisBases := ⟨Over.mk p, hd⟩
  let c : _root_.ConnectedComponents (Spec (CommRingCat.of Ω)) :=
    .mk (Classical.arbitrary _)
  apply translate_eq_iff_of_naturalIso
    (disconnectedClassTowerConnectedIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor X hp c)
    (CompactOpenLevel.normalInverseArrow U V hVU g)
    (CompactOpenLevel.normalInverseArrow U V hVU k) _ _ x
  exact unpointed_identityPoint_normalTranslate_eq_iff D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor p U V hVU hRigid hp g k

end GeometricTest

local notation "testBase" => cmGeometricTestBase D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality

include dualityNaturality polarizationStability in
/-- The named relative dual assertions admit the actual field spectrum and
transfer the equality criterion to its original disconnected tower. -/
theorem cmGeometricTestBase_normalTranslate_eq_iff
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (p : Spec (CommRingCat.of Ω) ⟶ Spec (.of F))
    (U V : HarrisLevel D) (hVU : V.subgroup ≤ U.subgroup)
    [(V.subgroup.subgroupOf U.subgroup).Normal]
    (hRigid : Rigid U) (g k : U.subgroup)
    (x : (distower (testBase existence geometry p)).obj V) :
    (distower (testBase existence geometry p)).map
        (CompactOpenLevel.normalInverseArrow U V hVU g) x =
      (distower (testBase existence geometry p)).map
        (CompactOpenLevel.normalInverseArrow U V hVU k) x ↔
      (g : U.subgroup ⧸ V.subgroup.subgroupOf U.subgroup) = k := by
  let : IsLocallyNoetherian (Over.mk p).left :=
    show IsLocallyNoetherian (Spec (CommRingCat.of Ω)) from inferInstance
  let : ConnectedSpace (Over.mk p).left :=
    show ConnectedSpace (Spec (CommRingCat.of Ω)) from inferInstance
  have hp : admissible (Over.mk p) :=
    (admissibleCMBase_iff_dualGeometry D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (Over.mk p)).mpr
        (fun B => ⟨existence _ B, geometry _ B (existence _ B)⟩)
  exact disconnected_identityPoint_normalTranslate_eq_iff D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor p U V hVU hRigid hp
    (testBase existence geometry p).property g k x

local notation "baseAction" => representedCMNormalQuotientBaseAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
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

/-- The exact representing isomorphism transfers equality of the original
subgroup translations to equality of their original residual classes. -/
theorem representedCMGeometricHom_normalTranslate_eq_iff
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (p : Spec (CommRingCat.of Ω) ⟶ Spec (.of F))
    (hRigid : Rigid U.obj) (g k : U.obj.subgroup)
    (x : testBase existence geometry p ⟶ (R V).base) :
    x ≫ (baseAction R U V hVU).ρ (QuotientGroup.mk g) =
      x ≫ (baseAction R U V hVU).ρ (QuotientGroup.mk k) ↔
      (g : SmallCMResidualGroup D U V) = k := by
  let S : DisBases := testBase existence geometry p
  let qx : (distower S).obj V.obj :=
    (R V).represents.hom.app (Opposite.op S) (ULift.up x)
  have he := cmGeometricTestBase_normalTranslate_eq_iff D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor existence geometry p
    U.obj V.obj hVU hRigid g k qx
  constructor
  · intro hx
    apply he.mp
    change ((smallLevelClassPresheafTower D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor).map
        (smallCMNormalInverseArrow D U V hVU g)).app (Opposite.op S) qx =
      ((smallLevelClassPresheafTower D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor).map
        (smallCMNormalInverseArrow D U V hVU k)).app (Opposite.op S) qx
    dsimp only [qx]
    rw [← representedCMNormalQuotientBaseAction_mk_classes D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor R U V hVU g S x,
      ← representedCMNormalQuotientBaseAction_mk_classes D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor R U V hVU k S x, hx]
  · intro hg
    rw [hg]

/-- Postcomposing a geometric-test morphism with the original residual action
is injective in the residual element, under actual fieldwise coarse rigidity. -/
theorem representedCMGeometricHom_normalTranslate_injective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (p : Spec (CommRingCat.of Ω) ⟶ Spec (.of F))
    (hRigid : Rigid U.obj)
    (x : testBase existence geometry p ⟶ (R V).base) :
    Function.Injective (fun g : SmallCMResidualGroup D U V =>
      x ≫ (baseAction R U V hVU).ρ g) := by
  intro g k
  induction g using QuotientGroup.induction_on with
  | H g =>
    induction k using QuotientGroup.induction_on with
    | H k =>
      exact (representedCMGeometricHom_normalTranslate_eq_iff D C preservation
        composition unitCoherence associativity comparison symmetry stability square
        universality dualityNaturality polarizationStability compatibility h htor
        R U V hVU existence geometry p hRigid g k x).mp

/-- The unchanged residual action is free on actual maps from every
algebraically closed field spectrum, under the explicit coarse rigidity. -/
theorem representedCMGeometricPoint_normalTranslate_injective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (hRigid : Rigid U.obj)
    (a : Spec (CommRingCat.of Ω) ⟶ (schemes R).obj V) :
    Function.Injective (fun g : SmallCMResidualGroup D U V =>
      a ≫ (quotientAction R U V hVU).ρ g) := by
  let p := a ≫ (R V).base.obj.hom
  let x : testBase existence geometry p ⟶ (R V).base :=
    ObjectProperty.homMk (Over.homMk a rfl)
  intro g k hgk
  apply representedCMGeometricHom_normalTranslate_injective D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    R U V hVU existence geometry p hRigid x
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact hgk

/-- The original residual action identifies its original residual group with
the exact geometric Hom fiber through a supplied fine geometric point. -/
def representedCMGeometricFiberEquiv
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (hRigid : Rigid U.obj)
    (a : Spec (CommRingCat.of Ω) ⟶ (schemes R).obj V) :
    SmallCMResidualGroup D U V ≃
      {b : Spec (CommRingCat.of Ω) ⟶ (schemes R).obj V //
        b ≫ projection R U V hVU = a ≫ projection R U V hVU} :=
  Equiv.ofBijective
    (fun g => ⟨a ≫ (quotientAction R U V hVU).ρ g, by
      rw [Category.assoc, representedCMNormalProjection_invariant]⟩)
    ⟨by
      intro g k hgk
      exact representedCMGeometricPoint_normalTranslate_injective D C preservation
        composition unitCoherence associativity comparison symmetry stability square
        universality dualityNaturality polarizationStability compatibility h htor
        R U V hVU existence geometry hRigid a (congrArg Subtype.val hgk),
    by
      intro b
      obtain ⟨g, hg⟩ := representedCMGeometricPoint_exists_normalTranslate D C preservation
        composition unitCoherence associativity comparison symmetry stability square
        universality dualityNaturality polarizationStability compatibility h htor
        R U V hVU existence geometry a b.val b.property.symm
      exact ⟨g, Subtype.ext hg⟩⟩

/-- The forward equivalence uses exactly the already defined residual action. -/
@[simp] theorem representedCMGeometricFiberEquiv_apply
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (hRigid : Rigid U.obj)
    (a : Spec (CommRingCat.of Ω) ⟶ (schemes R).obj V)
    (g : SmallCMResidualGroup D U V) :
    (representedCMGeometricFiberEquiv D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R U V hVU existence geometry
      hRigid a g).val = a ≫ (quotientAction R U V hVU).ρ g := rfl

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

/-- The identical chosen representations defining `cmSchemeTower` carry a
geometrically free original residual action under explicit coarse rigidity. -/
theorem cmGeometricPoint_normalTranslate_injective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (hRigid : Rigid U.obj)
    (a : Spec (CommRingCat.of Ω) ⟶ (chosenSchemes q).obj V) :
    Function.Injective (fun g : SmallCMResidualGroup D U V =>
      a ≫ (chosenAction q).ρ g) :=
  representedCMGeometricPoint_normalTranslate_injective D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry hRigid a

/-- Specialize the geometric Hom fiber equivalence to the exact chosen CM
tower, with no second choice of representations or residual action. -/
def cmGeometricFiberEquiv
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (hRigid : Rigid U.obj)
    (a : Spec (CommRingCat.of Ω) ⟶ (chosenSchemes q).obj V) :
    SmallCMResidualGroup D U V ≃
      {b : Spec (CommRingCat.of Ω) ⟶ (chosenSchemes q).obj V //
        b ≫ (chosenSchemes q).map (smallCMInclusion D hVU) =
          a ≫ (chosenSchemes q).map (smallCMInclusion D hVU)} :=
  representedCMGeometricFiberEquiv D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor (chosenReps q) U V hVU
    existence geometry hRigid a

/-- The chosen-tower equivalence retains the original forward action formula. -/
@[simp] theorem cmGeometricFiberEquiv_apply
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (hRigid : Rigid U.obj)
    (a : Spec (CommRingCat.of Ω) ⟶ (chosenSchemes q).obj V)
    (g : SmallCMResidualGroup D U V) :
    (cmGeometricFiberEquiv D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U V hVU q existence geometry
      hRigid a g).val = a ≫ (chosenAction q).ρ g := rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
