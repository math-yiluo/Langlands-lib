import Langlands.Sheaf.Renard.SectionActions
import Langlands.Sheaf.Renard.StalkActions
import Langlands.Sheaf.Renard.CompatibleTestActions
import Langlands.Sheaf.Renard.CompactSectionTestModule

/-!
# Compatible test actions on the original compact sections

Renard III.3.1: the existing compact-section representation is compatible
with the existing pointwise test action and the canonical complex scalars.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.CompactSectionActions

open CategoryTheory Opposite
open Langlands.Algebra Langlands.HarmonicAnalysis
open Langlands.Sheaf.Equivariant
open Langlands.Sheaf.Renard.SectionActions
open Langlands.Sheaf.Renard.CompatibleTestActions
open Langlands.Sheaf.Renard.CompactSectionTestModule

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {X : Type} [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

local instance compactTestModule (F : ActionSheaf G X) :
    NonUnitalModule (PointwiseTestAlgebra.Carrier X)
      (CompactSupport.submodule (CompactSections.ordinary F.obj)) :=
  CompactSectionTestModule.testModule (underlying F)

local instance compactScalarTower (F : ActionSheaf G X) :
    IsScalarTower ℂ (PointwiseTestAlgebra.Carrier X)
      (CompactSupport.submodule (CompactSections.ordinary F.obj)) :=
  CompactSectionTestModule.isScalarTower (underlying F)

/-- The original section action has the original labelled-stalk transport formula. -/
theorem global_germ_transport (F : ActionSheaf G X) (g : G)
    (s : F.obj.obj (op ActionOpens.top)) (x : X) :
    (CompactSections.ordinary F.obj).Γgerm x (globalRepresentation F g s) =
      (Godement.stalkPull F.obj g⁻¹ x (g⁻¹ • x) rfl).hom
        ((CompactSections.ordinary F.obj).Γgerm (g⁻¹ • x) s) :=
  (congrArg (fun f => f.hom s)
    (Godement.germ_stalkPull_arrow F.obj (ActionOpens.sectionArrow g)
      x (g⁻¹ • x) rfl trivial)).symm

/-- The source covariance formula for the actual compact sections. -/
theorem action_compatible (F : ActionSheaf G X) (g : G)
    (f : PointwiseTestAlgebra.Carrier X)
    (s : CompactSupport.submodule (CompactSections.ordinary F.obj)) :
    compactRepresentation F g (f • s) =
      testRepresentation g f • compactRepresentation F g s := by
  apply Subtype.ext
  apply VectorSheafScalars.ext_germ (underlying F)
  intro x hx
  change (CompactSections.ordinary F.obj).Γgerm x
      (globalRepresentation F g
        (VectorSheafScalars.smul (underlying F) (testScalar f) s.val)) =
    (CompactSections.ordinary F.obj).Γgerm x
      (VectorSheafScalars.smul (underlying F) (testScalar (testRepresentation g f))
        (globalRepresentation F g s.val))
  erw [global_germ_transport, Γgerm_smul (underlying F), map_smul,
    Γgerm_smul (underlying F), global_germ_transport]
  rfl

variable (hX : Langlands.Topology.IsLocallyProfinite X)

/-- The module object is exactly the published ordinary compact-section object. -/
abbrev moduleObject (F : ActionSheaf G X) :=
  (compactSectionFunctor hX).obj (underlying F)

omit [TopologicalSpace G] [ContinuousSMul G X] in
/-- Recovered complex multiplication is the original compact-section multiplication. -/
theorem canonicalScalar_eq (F : ActionSheaf G X) (c : ℂ)
    (s : CompactSupport.submodule (CompactSections.ordinary F.obj)) :
    NondegenerateScalars.scalarMul ℂ (moduleObject hX F).property c s = c • s :=
  NondegenerateScalars.scalarMul_eq_of_compatible ℂ
    (M := CompactSupport.submodule (CompactSections.ordinary F.obj))
    (isNondegenerate (underlying F) hX) c s

/-- The same group operators, complex-linear for the canonical module structure. -/
def canonicalAction (F : ActionSheaf G X) :
    letI := NondegenerateScalars.module ℂ PointwiseTestAlgebra.isIdempotented
      (moduleObject hX F).property
    Representation ℂ G (moduleObject hX F).obj := by
  letI := NondegenerateScalars.module ℂ PointwiseTestAlgebra.isIdempotented
    (moduleObject hX F).property
  refine
    { toFun := fun g =>
        { toFun := fun s => compactRepresentation F g s
          map_add' := fun s t => map_add (compactRepresentation F g) s t
          map_smul' := fun c s => ?_ }
      map_one' := ?_
      map_mul' := fun g k => ?_ }
  · change compactRepresentation F _
        (NondegenerateScalars.scalarMul ℂ (moduleObject hX F).property c s) =
      NondegenerateScalars.scalarMul ℂ (moduleObject hX F).property c
        (compactRepresentation F _ s)
    rw [canonicalScalar_eq, canonicalScalar_eq, map_smul]
  · ext s
    change compactRepresentation F 1 s = s
    simp
  · ext s
    exact LinearMap.congr_fun (map_mul (compactRepresentation F) g k) s

/-- Compact sections with their original tests and their original group operators. -/
def compatibleObject (F : ActionSheaf G X) :
    CompatibleTestAction.{uG, 0, 0} G X where
  module := moduleObject hX F
  action := canonicalAction hX F
  compatible := action_compatible F

/-- The original compact-section map preserves tests and group operators. -/
def compatibleMap {F F' : ActionSheaf G X} (φ : F ⟶ F') :
    compatibleObject hX F ⟶ compatibleObject hX F' where
  moduleHom := (compactSectionFunctor hX).map
    ((toSheaf G X (ModuleCat.{0} ℂ)).map φ)
  comm g s := LinearMap.congr_fun ((CompactSections.map φ).isIntertwining' g) s

/-- The equivariant refinement of the published ordinary compact-section functor. -/
def functor : ActionSheaf G X ⥤ CompatibleTestAction.{uG, 0, 0} G X where
  obj := compatibleObject hX
  map := compatibleMap hX
  map_id F := by
    apply CompatibleTestAction.Hom.ext
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro s
    rfl
  map_comp φ ψ := by
    apply CompatibleTestAction.Hom.ext
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro s
    rfl

/-- Forgetting group actions gives precisely the existing ordinary functor. -/
def forgetIso :
    functor (G := G) hX ⋙ CompatibleTestAction.toTestModule G X ≅
      toSheaf G X (ModuleCat.{0} ℂ) ⋙ compactSectionFunctor hX :=
  Iso.refl _

/-- Smoothness on the entire original module, with its compatible group action. -/
def smoothProperty : ObjectProperty (CompatibleTestAction.{uG, 0, 0} G X) :=
  fun M => letI := M.complexModule; Langlands.IsSmooth M.action

/-- The existing compatible objects whose whole original representation is smooth. -/
abbrev SmoothCompatibleTestAction :=
  (smoothProperty (G := G) (X := X)).FullSubcategory

/-- Renard smooth action sheaves give smooth compatible actions on all compact sections. -/
def smoothFunctor :
    SmoothActionSheaf G X ⥤ SmoothCompatibleTestAction (G := G) (X := X) :=
  (smoothProperty (G := G) (X := X)).lift
    (smoothActionInclusion G X ⋙ functor hX)
    (fun F => F.property)

end Langlands.Sheaf.Renard.CompactSectionActions
