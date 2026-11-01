import Langlands.Shimura.PEL.HarrisTaylorCMHeckeSchemes
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Conjugate levels and actual normalized CM scheme isomorphisms -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.CompactOpenLevel

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The actual conjugate level `g⁻¹ U g`, with its compact open topology. -/
def conjugate (U : CompactOpenLevel G) (g : G) : CompactOpenLevel G where
  openSubgroup := U.openSubgroup.comap (MulAut.conj g).toMonoidHom
    (by change Continuous (fun x : G => g * x * g⁻¹); fun_prop)
  isCompact := by
    let e : G ≃ₜ G := (Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)
    exact e.isCompact_preimage.mpr U.isCompact

@[simp] theorem mem_conjugate (U : CompactOpenLevel G) (g x : G) :
    x ∈ (conjugate U g).subgroup ↔ g * x * g⁻¹ ∈ U.subgroup := Iff.rfl

/-- Right translation by `g` and its actual inverse are inverse transporters. -/
def conjugationIso (U : CompactOpenLevel G) (g : G) : U ≅ conjugate U g where
  hom := ⟨g, fun x hx => by
    change g * (g⁻¹ * x * g) * g⁻¹ ∈ U.subgroup
    simpa [mul_assoc] using hx⟩
  inv := ⟨g⁻¹, fun x hx => by
    change g * x * g⁻¹ ∈ U.subgroup at hx
    simpa using hx⟩
  hom_inv_id := by apply Arrow.ext; exact mul_inv_cancel g
  inv_hom_id := by apply Arrow.ext; exact inv_mul_cancel g

@[simp] theorem conjugationIso_hom_element (U : CompactOpenLevel G) (g : G) :
    (conjugationIso U g).hom.element = g := rfl

@[simp] theorem conjugationIso_inv_element (U : CompactOpenLevel G) (g : G) :
    (conjugationIso U g).inv.element = g⁻¹ := rfl

/-- Conjugation takes an actual inclusion to an actual inclusion. -/
def conjugateInclusion {U V : CompactOpenLevel G} (hUV : U.subgroup ≤ V.subgroup)
    (g : G) : conjugate U g ⟶ conjugate V g :=
  inclusion (fun _ hx => hUV hx)

/-- Conjugation commutes with level forgetting in the transporter category. -/
theorem conjugationIso_naturality {U V : CompactOpenLevel G}
    (hUV : U.subgroup ≤ V.subgroup) (g : G) :
    (conjugationIso U g).hom ≫ conjugateInclusion hUV g =
      inclusion hUV ≫ (conjugationIso V g).hom := by
  apply Arrow.ext
  exact (mul_one g).trans (one_mul g).symm

end Langlands.Shimura.CompactOpenLevel

namespace Langlands.Shimura.AlgebraInvolution

variable {B : Type*} [Ring B] [Algebra ℚ B]
  {σ : AlgebraInvolution ℚ B} [Module.Finite ℚ B]

/-- The same finite place certifies smallness of every actual conjugate level. -/
theorem LevelSmallAt.conjugate
    {U : CompactOpenLevel σ.FiniteAdelicPointsᵐᵒᵖ} {v : Global.FinitePlace ℚ}
    (hU : σ.LevelSmallAt U v) (g : σ.FiniteAdelicPointsᵐᵒᵖ) :
    σ.LevelSmallAt (CompactOpenLevel.conjugate U g) v := by
  intro x hx hfin
  let a := σ.pointsMap (finiteEvaluation v) (MulOpposite.unop g)
  have hconj : IsOfFinOrder
      (σ.pointsMap (finiteEvaluation v) (MulOpposite.unop (g * x * g⁻¹))) := by
    simpa [a, MulAut.conj_apply, map_mul, MulOpposite.unop_mul, mul_assoc] using
      (MulAut.conj a⁻¹).toMonoidHom.isOfFinOrder hfin
  have hz := hU (g * x * g⁻¹) hx hconj
  have hz' := congrArg (fun z => a * z * a⁻¹) hz
  simpa [a, map_mul, MulOpposite.unop_mul, mul_assoc] using hz'

/-- Sufficient smallness is preserved by actual finite-adelic conjugation. -/
theorem LevelSufficientlySmall.conjugate
    {U : CompactOpenLevel σ.FiniteAdelicPointsᵐᵒᵖ}
    (hU : σ.LevelSufficientlySmall U) (g : σ.FiniteAdelicPointsᵐᵒᵖ) :
    σ.LevelSufficientlySmall (CompactOpenLevel.conjugate U g) := by
  obtain ⟨v, hv⟩ := hU
  exact ⟨v, hv.conjugate g⟩

end Langlands.Shimura.AlgebraInvolution

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

/-- The actual conjugate sufficiently small level in the original opposite group. -/
def smallCMConjugateLevel (U : SmallCMLevel D) (g : OriginalGroup) : SmallCMLevel D := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  exact ⟨CompactOpenLevel.conjugate U.obj g, U.property.conjugate g⟩

/-- The conjugating element and its inverse give an isomorphism of small levels. -/
def smallCMConjugationIso (U : SmallCMLevel D) (g : OriginalGroup) :
    U ≅ smallCMConjugateLevel D U g := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  exact ObjectProperty.isoMk _ (CompactOpenLevel.conjugationIso U.obj g)

omit [IsCMField F] [IsScalarTower E F A] in
@[simp] theorem smallCMConjugationIso_hom_element (U : SmallCMLevel D)
    (g : OriginalGroup) : (smallCMConjugationIso D U g).hom.hom.element = g := rfl

omit [IsCMField F] [IsScalarTower E F A] in
@[simp] theorem smallCMConjugationIso_inv_element (U : SmallCMLevel D)
    (g : OriginalGroup) : (smallCMConjugationIso D U g).inv.hom.element = g⁻¹ := rfl

/-- Conjugation of a genuine small-level inclusion. -/
def smallCMConjugateInclusion {U V : SmallCMLevel D}
    (hUV : U.obj.subgroup ≤ V.obj.subgroup) (g : OriginalGroup) :
    smallCMConjugateLevel D U g ⟶ smallCMConjugateLevel D V g := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  exact ObjectProperty.homMk (CompactOpenLevel.conjugateInclusion hUV g)

omit [IsCMField F] [IsScalarTower E F A] in
/-- Conjugation and forgetting commute at the original small levels. -/
theorem smallCMConjugationIso_naturality {U V : SmallCMLevel D}
    (hUV : U.obj.subgroup ≤ V.obj.subgroup) (g : OriginalGroup) :
    (smallCMConjugationIso D U g).hom ≫ smallCMConjugateInclusion D hUV g =
      smallCMInclusion D hUV ≫ (smallCMConjugationIso D V g).hom := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  apply ObjectProperty.hom_ext
  exact CompactOpenLevel.conjugationIso_naturality hUV g

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

/-- The actual conjugation isomorphism of represented admissible CM bases. -/
def representedCMBaseConjugationIso (U : SmallCMLevel D) (g : OriginalGroup) :
    (baseTower R).obj U ≅ (baseTower R).obj (smallCMConjugateLevel D U g) :=
  (baseTower R).mapIso (smallCMConjugationIso D U g)

/-- The actual scheme isomorphism is derived from the existing represented tower. -/
def representedCMSchemeConjugationIso (U : SmallCMLevel D) (g : OriginalGroup) :
    (schemes R).obj U ≅ (schemes R).obj (smallCMConjugateLevel D U g) :=
  (schemes R).mapIso (smallCMConjugationIso D U g)

local notation "conjIso" => representedCMSchemeConjugationIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- The forward isomorphism lies over the original CM field. -/
theorem representedCMSchemeConjugationIso_hom_over (U : SmallCMLevel D)
    (g : OriginalGroup) :
    (conjIso R U g).hom ≫ (R (smallCMConjugateLevel D U g)).base.obj.hom =
      (R U).base.obj.hom :=
  representedCMSchemeTower_over D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor R (smallCMConjugationIso D U g).hom

/-- The actual inverse also lies over the same CM field. -/
theorem representedCMSchemeConjugationIso_inv_over (U : SmallCMLevel D)
    (g : OriginalGroup) :
    (conjIso R U g).inv ≫ (R U).base.obj.hom =
      (R (smallCMConjugateLevel D U g)).base.obj.hom :=
  representedCMSchemeTower_over D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor R (smallCMConjugationIso D U g).inv

/-- On every actual admissible test, the forward isomorphism is the existing
right translation by the specified original-group element. -/
theorem representedCMBaseConjugationIso_hom_classes (U : SmallCMLevel D)
    (g : OriginalGroup) (S : DisBases) (f : S ⟶ (baseTower R).obj U) :
    (R (smallCMConjugateLevel D U g)).represents.hom.app (Opposite.op S)
        (ULift.up (f ≫ (baseTower R).map (smallCMConjugationIso D U g).hom)) =
      ((moduli).map (smallCMConjugationIso D U g).hom).app (Opposite.op S)
        ((R U).represents.hom.app (Opposite.op S) (ULift.up f)) :=
  representedCMBaseTower_map_classes D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor R (smallCMConjugationIso D U g).hom S f

/-- The inverse has the original right-translation interpretation by `g⁻¹`. -/
theorem representedCMBaseConjugationIso_inv_classes (U : SmallCMLevel D)
    (g : OriginalGroup) (S : DisBases)
    (f : S ⟶ (baseTower R).obj (smallCMConjugateLevel D U g)) :
    (R U).represents.hom.app (Opposite.op S)
        (ULift.up (f ≫ (baseTower R).map (smallCMConjugationIso D U g).inv)) =
      ((moduli).map (smallCMConjugationIso D U g).inv).app (Opposite.op S)
        ((R (smallCMConjugateLevel D U g)).represents.hom.app (Opposite.op S)
          (ULift.up f)) :=
  representedCMBaseTower_map_classes D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor R (smallCMConjugationIso D U g).inv S f

/-- The actual conjugation isomorphisms commute with forgetting level. -/
theorem representedCMSchemeConjugationIso_naturality {U V : SmallCMLevel D}
    (hUV : U.obj.subgroup ≤ V.obj.subgroup) (g : OriginalGroup) :
    (conjIso R U g).hom ≫ (schemes R).map (smallCMConjugateInclusion D hUV g) =
      (schemes R).map (smallCMInclusion D hUV) ≫ (conjIso R V g).hom := by
  change (schemes R).map _ ≫ (schemes R).map _ =
    (schemes R).map _ ≫ (schemes R).map _
  rw [← Functor.map_comp, ← Functor.map_comp, smallCMConjugationIso_naturality]

variable (R' : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)

local notation "compareReps" => representedCMSchemeTowerComparison D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- The forward conjugation square commutes under the canonical change of
representing choices for the same exact moduli presheaves. -/
theorem representedCMSchemeConjugationIso_hom_comparison (U : SmallCMLevel D)
    (g : OriginalGroup) :
    (conjIso R U g).hom ≫ (compareReps R R').hom.app (smallCMConjugateLevel D U g) =
      (compareReps R R').hom.app U ≫ (conjIso R' U g).hom :=
  (compareReps R R').hom.naturality (smallCMConjugationIso D U g).hom

/-- The same canonical comparison commutes with the actual inverse. -/
theorem representedCMSchemeConjugationIso_inv_comparison (U : SmallCMLevel D)
    (g : OriginalGroup) :
    (conjIso R U g).inv ≫ (compareReps R R').hom.app U =
      (compareReps R R').hom.app (smallCMConjugateLevel D U g) ≫
        (conjIso R' U g).inv :=
  (compareReps R R').hom.naturality (smallCMConjugationIso D U g).inv

/-- The actual scheme conjugation isomorphism conditional on exactly the
existing representability proposition, with no new scheme-map input. -/
def cmSchemeConjugationIso
    (q : CMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (U : SmallCMLevel D) (g : OriginalGroup) :
    (cmSchemeTower D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q).obj U ≅
    (cmSchemeTower D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q).obj (smallCMConjugateLevel D U g) :=
  conjIso (chosenCMLevelRepresentation D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q) U g

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
