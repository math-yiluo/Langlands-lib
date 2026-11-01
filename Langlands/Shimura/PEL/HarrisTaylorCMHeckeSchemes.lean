import Langlands.Shimura.PEL.HarrisTaylorCMSchemeLevels

/-! # Actual scheme Hecke spans from exact normalized CM representations -/

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

local notation "OriginalGroup" => D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ

/-- The actual Hecke intersection, carrying the inherited local smallness proof. -/
def smallCMHeckeLevel (U V : SmallCMLevel D) (g : OriginalGroup) : SmallCMLevel D := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  exact ⟨CompactOpenLevel.heckeLevel U.obj V.obj g,
    U.property.heckeLevel V.obj g⟩

/-- The identity transporter for a genuine inclusion of small levels. -/
def smallCMInclusion {U V : SmallCMLevel D}
    (hUV : U.obj.subgroup ≤ V.obj.subgroup) : U ⟶ V :=
  ObjectProperty.homMk (CompactOpenLevel.inclusion hUV)

/-- The first Hecke transporter forgets the finer intersection level. -/
def smallCMHeckeLeft (U V : SmallCMLevel D) (g : OriginalGroup) :
    smallCMHeckeLevel D U V g ⟶ U := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  exact ObjectProperty.homMk (CompactOpenLevel.heckeLeft U.obj V.obj g)

/-- The second Hecke transporter is represented by the specified adelic element. -/
def smallCMHeckeRight (U V : SmallCMLevel D) (g : OriginalGroup) :
    smallCMHeckeLevel D U V g ⟶ V := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  exact ObjectProperty.homMk (CompactOpenLevel.heckeRight U.obj V.obj g)

omit [IsCMField F] [IsScalarTower E F A] in
@[simp] theorem smallCMHeckeLeft_element (U V : SmallCMLevel D) (g : OriginalGroup) :
    (smallCMHeckeLeft D U V g).hom.element = 1 := rfl

omit [IsCMField F] [IsScalarTower E F A] in
@[simp] theorem smallCMHeckeRight_element (U V : SmallCMLevel D) (g : OriginalGroup) :
    (smallCMHeckeRight D U V g).hom.element = g := rfl

/-- Refining either endpoint gives an actual inclusion of Hecke intersections. -/
def smallCMHeckeRefinement {U' V' U V : SmallCMLevel D}
    (hU : U'.obj.subgroup ≤ U.obj.subgroup)
    (hV : V'.obj.subgroup ≤ V.obj.subgroup) (g : OriginalGroup) :
    smallCMHeckeLevel D U' V' g ⟶ smallCMHeckeLevel D U V g := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  exact smallCMInclusion D (fun _ hk => ⟨hU hk.1, hV hk.2⟩)

omit [IsCMField F] [IsScalarTower E F A] in
/-- Refinement commutes with the first transporter leg. -/
theorem smallCMHeckeRefinement_left {U' V' U V : SmallCMLevel D}
    (hU : U'.obj.subgroup ≤ U.obj.subgroup)
    (hV : V'.obj.subgroup ≤ V.obj.subgroup) (g : OriginalGroup) :
    smallCMHeckeRefinement D hU hV g ≫ smallCMHeckeLeft D U V g =
      smallCMHeckeLeft D U' V' g ≫ smallCMInclusion D hU := by
  apply ObjectProperty.hom_ext
  apply CompactOpenLevel.Arrow.ext
  rfl

omit [IsCMField F] [IsScalarTower E F A] in
/-- Refinement commutes with the translating transporter leg. -/
theorem smallCMHeckeRefinement_right {U' V' U V : SmallCMLevel D}
    (hU : U'.obj.subgroup ≤ U.obj.subgroup)
    (hV : V'.obj.subgroup ≤ V.obj.subgroup) (g : OriginalGroup) :
    smallCMHeckeRefinement D hU hV g ≫ smallCMHeckeRight D U V g =
      smallCMHeckeRight D U' V' g ≫ smallCMInclusion D hV := by
  apply ObjectProperty.hom_ext
  apply CompactOpenLevel.Arrow.ext
  exact (one_mul g).trans (mul_one g).symm

omit [IsCMField F] [IsScalarTower E F A] in
/-- Refining both endpoints by the identity gives the identity transporter. -/
@[simp] theorem smallCMHeckeRefinement_refl (U V : SmallCMLevel D) (g : OriginalGroup) :
    smallCMHeckeRefinement D (le_refl U.obj.subgroup) (le_refl V.obj.subgroup) g =
      𝟙 (smallCMHeckeLevel D U V g) := by
  apply ObjectProperty.hom_ext
  apply CompactOpenLevel.Arrow.ext
  rfl

omit [IsCMField F] [IsScalarTower E F A] in
/-- Successive refinements agree with the direct inclusion of intersections. -/
theorem smallCMHeckeRefinement_trans {U₁ V₁ U₂ V₂ U₃ V₃ : SmallCMLevel D}
    (hU₁₂ : U₁.obj.subgroup ≤ U₂.obj.subgroup)
    (hV₁₂ : V₁.obj.subgroup ≤ V₂.obj.subgroup)
    (hU₂₃ : U₂.obj.subgroup ≤ U₃.obj.subgroup)
    (hV₂₃ : V₂.obj.subgroup ≤ V₃.obj.subgroup) (g : OriginalGroup) :
    smallCMHeckeRefinement D hU₁₂ hV₁₂ g ≫ smallCMHeckeRefinement D hU₂₃ hV₂₃ g =
      smallCMHeckeRefinement D (hU₁₂.trans hU₂₃) (hV₁₂.trans hV₂₃) g := by
  apply ObjectProperty.hom_ext
  apply CompactOpenLevel.Arrow.ext
  exact one_mul 1

local notation "moduli" => smallLevelClassPresheafTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "baseTower" => representedCMBaseTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "schemes" => representedCMSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

variable (R : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)

/-- The first actual scheme leg is obtained from the unique represented
forgetting transition; no scheme morphism is supplied as new data. -/
def representedCMHeckeLeft (U V : SmallCMLevel D) (g : OriginalGroup) :
    (schemes R).obj (smallCMHeckeLevel D U V g) ⟶ (schemes R).obj U :=
  (schemes R).map (smallCMHeckeLeft D U V g)

/-- The second actual scheme leg represents the existing right translation. -/
def representedCMHeckeRight (U V : SmallCMLevel D) (g : OriginalGroup) :
    (schemes R).obj (smallCMHeckeLevel D U V g) ⟶ (schemes R).obj V :=
  (schemes R).map (smallCMHeckeRight D U V g)

local notation "leftLeg" => representedCMHeckeLeft D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "rightLeg" => representedCMHeckeRight D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- The forgetting leg is an actual morphism over the original CM field. -/
theorem representedCMHeckeLeft_over (U V : SmallCMLevel D) (g : OriginalGroup) :
    leftLeg R U V g ≫ (R U).base.obj.hom =
      (R (smallCMHeckeLevel D U V g)).base.obj.hom :=
  representedCMSchemeTower_over D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor R (smallCMHeckeLeft D U V g)

/-- The translating leg is also over the original CM field. -/
theorem representedCMHeckeRight_over (U V : SmallCMLevel D) (g : OriginalGroup) :
    rightLeg R U V g ≫ (R V).base.obj.hom =
      (R (smallCMHeckeLevel D U V g)).base.obj.hom :=
  representedCMSchemeTower_over D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor R (smallCMHeckeRight D U V g)

/-- The two legs form a cone over the actual structure maps to `Spec F`.
This supplies the span and its equality over the base, without a pullback claim. -/
def representedCMHeckeSpan (U V : SmallCMLevel D) (g : OriginalGroup) :
    Limits.PullbackCone (R U).base.obj.hom (R V).base.obj.hom :=
  Limits.PullbackCone.mk (leftLeg R U V g) (rightLeg R U V g)
    ((representedCMHeckeLeft_over D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R U V g).trans
      (representedCMHeckeRight_over D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor R U V g).symm)

/-- On every actual admissible test scheme, the first leg acts by the
already constructed moduli forgetting map. -/
theorem representedCMHeckeLeft_classes (U V : SmallCMLevel D) (g : OriginalGroup)
    (S : DisBases) (f : S ⟶ (baseTower R).obj (smallCMHeckeLevel D U V g)) :
    (R U).represents.hom.app (Opposite.op S)
        (ULift.up (f ≫ (baseTower R).map (smallCMHeckeLeft D U V g))) =
      ((moduli).map (smallCMHeckeLeft D U V g)).app (Opposite.op S)
        ((R (smallCMHeckeLevel D U V g)).represents.hom.app (Opposite.op S)
          (ULift.up f)) :=
  representedCMBaseTower_map_classes D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor R (smallCMHeckeLeft D U V g) S f

/-- On every actual admissible test scheme, the second leg acts by the
existing original-Harris right transporter on CM classes. -/
theorem representedCMHeckeRight_classes (U V : SmallCMLevel D) (g : OriginalGroup)
    (S : DisBases) (f : S ⟶ (baseTower R).obj (smallCMHeckeLevel D U V g)) :
    (R V).represents.hom.app (Opposite.op S)
        (ULift.up (f ≫ (baseTower R).map (smallCMHeckeRight D U V g))) =
      ((moduli).map (smallCMHeckeRight D U V g)).app (Opposite.op S)
        ((R (smallCMHeckeLevel D U V g)).represents.hom.app (Opposite.op S)
          (ULift.up f)) :=
  representedCMBaseTower_map_classes D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor R (smallCMHeckeRight D U V g) S f

/-- The actual scheme map comparing two refined Hecke intersections. -/
def representedCMHeckeRefinement {U' V' U V : SmallCMLevel D}
    (hU : U'.obj.subgroup ≤ U.obj.subgroup)
    (hV : V'.obj.subgroup ≤ V.obj.subgroup) (g : OriginalGroup) :
    (schemes R).obj (smallCMHeckeLevel D U' V' g) ⟶
      (schemes R).obj (smallCMHeckeLevel D U V g) :=
  (schemes R).map (smallCMHeckeRefinement D hU hV g)

local notation "refineLeg" => representedCMHeckeRefinement D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- The first square of actual scheme Hecke spans commutes under refinement. -/
theorem representedCMHeckeRefinement_left {U' V' U V : SmallCMLevel D}
    (hU : U'.obj.subgroup ≤ U.obj.subgroup)
    (hV : V'.obj.subgroup ≤ V.obj.subgroup) (g : OriginalGroup) :
    refineLeg R hU hV g ≫ leftLeg R U V g =
      leftLeg R U' V' g ≫ (schemes R).map (smallCMInclusion D hU) := by
  change (schemes R).map _ ≫ (schemes R).map _ =
    (schemes R).map _ ≫ (schemes R).map _
  rw [← Functor.map_comp, ← Functor.map_comp, smallCMHeckeRefinement_left]

/-- The translating square of actual scheme spans commutes under refinement. -/
theorem representedCMHeckeRefinement_right {U' V' U V : SmallCMLevel D}
    (hU : U'.obj.subgroup ≤ U.obj.subgroup)
    (hV : V'.obj.subgroup ≤ V.obj.subgroup) (g : OriginalGroup) :
    refineLeg R hU hV g ≫ rightLeg R U V g =
      rightLeg R U' V' g ≫ (schemes R).map (smallCMInclusion D hV) := by
  change (schemes R).map _ ≫ (schemes R).map _ =
    (schemes R).map _ ≫ (schemes R).map _
  rw [← Functor.map_comp, ← Functor.map_comp, smallCMHeckeRefinement_right]

/-- Identity refinement gives the identity on the actual middle scheme. -/
@[simp] theorem representedCMHeckeRefinement_refl (U V : SmallCMLevel D)
    (g : OriginalGroup) :
    refineLeg R (le_refl U.obj.subgroup) (le_refl V.obj.subgroup) g =
      𝟙 ((schemes R).obj (smallCMHeckeLevel D U V g)) := by
  change (schemes R).map _ = _
  rw [smallCMHeckeRefinement_refl]
  exact (schemes R).map_id _

/-- The scheme maps for successive refinements compose to the direct map. -/
theorem representedCMHeckeRefinement_trans {U₁ V₁ U₂ V₂ U₃ V₃ : SmallCMLevel D}
    (hU₁₂ : U₁.obj.subgroup ≤ U₂.obj.subgroup)
    (hV₁₂ : V₁.obj.subgroup ≤ V₂.obj.subgroup)
    (hU₂₃ : U₂.obj.subgroup ≤ U₃.obj.subgroup)
    (hV₂₃ : V₂.obj.subgroup ≤ V₃.obj.subgroup) (g : OriginalGroup) :
    refineLeg R hU₁₂ hV₁₂ g ≫ refineLeg R hU₂₃ hV₂₃ g =
      refineLeg R (hU₁₂.trans hU₂₃) (hV₁₂.trans hV₂₃) g := by
  change (schemes R).map _ ≫ (schemes R).map _ = (schemes R).map _
  rw [← Functor.map_comp, smallCMHeckeRefinement_trans]

variable (R' : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)

local notation "compareReps" => representedCMSchemeTowerComparison D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- The first legs commute with the canonical change of representing choices. -/
theorem representedCMHeckeLeft_comparison (U V : SmallCMLevel D) (g : OriginalGroup) :
    leftLeg R U V g ≫ (compareReps R R').hom.app U =
      (compareReps R R').hom.app (smallCMHeckeLevel D U V g) ≫ leftLeg R' U V g :=
  (compareReps R R').hom.naturality (smallCMHeckeLeft D U V g)

/-- The second legs commute with the same canonical change of choices. -/
theorem representedCMHeckeRight_comparison (U V : SmallCMLevel D) (g : OriginalGroup) :
    rightLeg R U V g ≫ (compareReps R R').hom.app V =
      (compareReps R R').hom.app (smallCMHeckeLevel D U V g) ≫ rightLeg R' U V g :=
  (compareReps R R').hom.naturality (smallCMHeckeRight D U V g)

/-- The first actual scheme leg, conditional on the exact existence proposition. -/
def cmHeckeLeft
    (q : CMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (U V : SmallCMLevel D) (g : OriginalGroup) :
    (cmSchemeTower D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q).obj (smallCMHeckeLevel D U V g) ⟶
    (cmSchemeTower D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q).obj U :=
  leftLeg (chosenCMLevelRepresentation D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q) U V g

/-- The translating actual scheme leg under exactly the same existence hypothesis. -/
def cmHeckeRight
    (q : CMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (U V : SmallCMLevel D) (g : OriginalGroup) :
    (cmSchemeTower D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q).obj (smallCMHeckeLevel D U V g) ⟶
    (cmSchemeTower D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q).obj V :=
  rightLeg (chosenCMLevelRepresentation D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q) U V g

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
