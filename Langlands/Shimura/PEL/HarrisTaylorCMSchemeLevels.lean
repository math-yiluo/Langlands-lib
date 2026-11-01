import Langlands.Shimura.PEL.HarrisTaylorCMRepresentabilityStatement
import Mathlib.CategoryTheory.Whiskering

/-! # Scheme towers derived from exact normalized CM representability -/

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

local notation "moduli" => smallLevelClassPresheafTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
variable (R : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)

/-- The actual tower of admissible CM schemes recovered from pointwise
representations. Every transition is the unique lifted Yoneda preimage of the
existing moduli transition. -/
def representedCMBaseTower : SmallCMLevel D ⥤ DisBases where
  obj U := (R U).base
  map {U V} k := (ULiftYoneda.fullyFaithful.{1} DisBases).preimage
    ((R U).represents.hom ≫ (moduli).map k ≫ (R V).represents.inv)
  map_id U := by
    apply (ULiftYoneda.fullyFaithful.{1} DisBases).map_injective
    simp
  map_comp k l := by
    apply (ULiftYoneda.fullyFaithful.{1} DisBases).map_injective
    simp [Category.assoc]

local notation "baseTower" => representedCMBaseTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- Representation is natural in the original small-level transporter category. -/
def representedCMBaseTowerRepresentation : baseTower R ⋙ uliftYoneda.{1} ≅ moduli :=
  NatIso.ofComponents (fun U => (R U).represents) (by
    intro U V k
    simp [representedCMBaseTower, Category.assoc])

/-- The actual scheme maps retain their structure maps to the CM field. -/
def representedCMOverTower : SmallCMLevel D ⥤ Over (Spec (.of F)) :=
  baseTower R ⋙ ObjectProperty.ι
    (ComponentwiseAdmissibleCMBase D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality)

/-- The underlying actual scheme tower. -/
def representedCMSchemeTower : SmallCMLevel D ⥤ Scheme :=
  representedCMOverTower D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor R ⋙ Over.forget (Spec (.of F))

/-- A transition commutes with the actual structure maps to `Spec F`. -/
theorem representedCMSchemeTower_over {U V : SmallCMLevel D} (k : U ⟶ V) :
    (representedCMSchemeTower D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R).map k ≫ (R V).base.obj.hom =
    (R U).base.obj.hom :=
  Over.w ((baseTower R).map k).hom

/-- Scheme-level transitions induce precisely the original maps on actual
CM classes, at every actual test scheme and every actual morphism to a level. -/
theorem representedCMBaseTower_map_classes {U V : SmallCMLevel D} (k : U ⟶ V)
    (S : DisBases) (f : S ⟶ (baseTower R).obj U) :
    (R V).represents.hom.app (Opposite.op S)
        (ULift.up (f ≫ (baseTower R).map k)) =
      ((moduli).map k).app (Opposite.op S)
        ((R U).represents.hom.app (Opposite.op S) (ULift.up f)) := by
  have e := (representedCMBaseTowerRepresentation D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor R).hom.naturality k
  exact congrArg
    (fun t : uliftYoneda.{1}.obj ((R U).base) ⟶ (moduli).obj V =>
      t.app (Opposite.op S) (ULift.up f)) e

/-- The Yoneda compatibility condition uniquely determines each actual map. -/
theorem representedCMBaseTower_map_unique {U V : SmallCMLevel D} (k : U ⟶ V)
    (f : (R U).base ⟶ (R V).base)
    (e : uliftYoneda.{1}.map f ≫ (R V).represents.hom =
      (R U).represents.hom ≫ (moduli).map k) :
    f = (baseTower R).map k := by
  apply (ULiftYoneda.fullyFaithful.{1} DisBases).map_injective
  apply (cancel_mono (R V).represents.hom).1
  simpa [representedCMBaseTower, Category.assoc] using e

/-- The resulting levels are smooth over the actual CM field. -/
instance representedCMOverTower_smooth (U : SmallCMLevel D) :
    Smooth ((representedCMOverTower D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R).obj U).hom :=
  (R U).smooth

/-- Each resulting level has the supplied actual projective-space immersion. -/
theorem representedCMOverTower_projective (U : SmallCMLevel D) :
    IsHProjective ((representedCMOverTower D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R).obj U).hom :=
  (R U).projective

variable (R' R'' : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)

/-- Two pointwise representations yield canonically isomorphic actual towers.
The comparison is induced by the identity of the same moduli presheaves. -/
def representedCMBaseTowerComparison : baseTower R ≅ baseTower R' :=
  NatIso.ofComponents
    (fun U => (ULiftYoneda.fullyFaithful.{1} DisBases).preimageIso
      ((R U).represents ≪≫ (R' U).represents.symm)) (by
    intro U V k
    apply (ULiftYoneda.fullyFaithful.{1} DisBases).map_injective
    simp [representedCMBaseTower, Category.assoc])

local notation "compareReps" => representedCMBaseTowerComparison D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- The canonical comparison preserves the specified interpretation of classes. -/
theorem representedCMBaseTowerComparison_represents (U : SmallCMLevel D) :
    uliftYoneda.{1}.map ((compareReps R R').hom.app U) ≫ (R' U).represents.hom =
      (R U).represents.hom := by
  simp [representedCMBaseTowerComparison, Category.assoc]

@[simp] theorem representedCMBaseTowerComparison_refl :
    compareReps R R = Iso.refl (baseTower R) := by
  apply Iso.ext
  apply NatTrans.ext
  funext U
  apply (ULiftYoneda.fullyFaithful.{1} DisBases).map_injective
  simp [representedCMBaseTowerComparison]

/-- Canonical comparisons obey the cocycle equation. -/
theorem representedCMBaseTowerComparison_trans :
    compareReps R R' ≪≫ compareReps R' R'' = compareReps R R'' := by
  apply Iso.ext
  apply NatTrans.ext
  funext U
  apply (ULiftYoneda.fullyFaithful.{1} DisBases).map_injective
  simp [representedCMBaseTowerComparison, Category.assoc]

/-- The canonical comparison is also an isomorphism of actual scheme towers. -/
def representedCMSchemeTowerComparison :
    representedCMSchemeTower D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R ≅
    representedCMSchemeTower D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R' :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerRight (compareReps R R')
      (ObjectProperty.ι (ComponentwiseAdmissibleCMBase D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality)))
    (Over.forget (Spec (.of F)))

/-- Choose the pointwise representing evidence from exactly the previously
stated existence proposition, without adding unconstrained transition maps. -/
def chosenCMLevelRepresentation
    (q : CMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor) (U : SmallCMLevel D) : CMLevelRepresentation D C
        preservation composition unitCoherence associativity comparison symmetry
        stability square universality dualityNaturality polarizationStability
        compatibility h htor U :=
  Classical.choice (q U)

local notation "chosen" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- The actual scheme levels, conditional on a proof of the exact existence
target. Identities and composition are proved by the Yoneda construction. -/
def cmSchemeTower
    (q : CMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor) : SmallCMLevel D ⥤ Scheme :=
  representedCMSchemeTower D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor (chosen q)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
