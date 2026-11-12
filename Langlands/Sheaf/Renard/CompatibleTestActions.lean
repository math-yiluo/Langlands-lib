import Langlands.HarmonicAnalysis.PointwiseTestModule
import Langlands.Representation.Category.Basic
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Compatible actions on the original pointwise test modules

Renard III.3.1 uses the action on `D(X)` by inverse pullback and
nondegenerate `D(X)`-modules with compatible linear group actions.
-/

noncomputable section

namespace Langlands.Sheaf.Renard.CompatibleTestActions

open CategoryTheory
open Langlands.Algebra Langlands.HarmonicAnalysis
open PointwiseTestAlgebra

universe uG uX uM

variable {G : Type uG} [Group G]
variable {X : Type uX} [TopologicalSpace X] [MulAction G X]
variable [ContinuousConstSMul G X]

/-- Inverse pullback on the actual pointwise compact test functions. -/
def testTranslate (g : G) (f : Carrier X) : Carrier X :=
  ⟨f.val.comap ⟨(g⁻¹ • ·), continuous_const_smul g⁻¹⟩,
    f.property.comp_homeomorph (Homeomorph.smul g⁻¹)⟩

@[simp]
theorem testTranslate_apply (g : G) (f : Carrier X) (x : X) :
    testTranslate g f x = f (g⁻¹ • x) := rfl

/-- The left representation on `D(X)`, retaining its published carrier. -/
def testRepresentation : Representation ℂ G (Carrier X) where
  toFun g :=
    { toFun := testTranslate g
      map_add' f h := by ext x; rfl
      map_smul' c f := by ext x; rfl }
  map_one' := by
    ext f x
    simp [testTranslate]
  map_mul' g h := by
    ext f x
    simp [testTranslate, mul_smul]

@[simp]
theorem testRepresentation_apply (g : G) (f : Carrier X) (x : X) :
    testRepresentation g f x = f (g⁻¹ • x) := rfl

theorem testRepresentation_mul (g : G) (f h : Carrier X) :
    testRepresentation g (f * h) =
      testRepresentation g f * testRepresentation g h := by
  ext x
  rfl

variable (G X)

/-- A published nondegenerate test module with a compatible linear group action.
Its complex module structure is the published canonical one on that same carrier. -/
structure CompatibleTestAction where
  module : NondegenerateModuleCat.{uX, uM} (Carrier X)
  action : letI := NondegenerateScalars.module ℂ isIdempotented module.property
    Representation ℂ G module.obj
  compatible : letI := NondegenerateScalars.module ℂ isIdempotented module.property
    ∀ (g : G) (f : Carrier X) (m : module.obj),
      action g (f • m) = testRepresentation g f • action g m

namespace CompatibleTestAction

variable {G X}

/-- Canonical complex scalars on the original additive module carrier. -/
abbrev complexModule (M : CompatibleTestAction.{uG, uX, uM} G X) :
    Module ℂ M.module.obj :=
  NondegenerateScalars.module ℂ isIdempotented M.module.property

/-- Read the original additive test-linear map of a published module morphism. -/
abbrev moduleMap {M N : NondegenerateModuleCat.{uX, uM} (Carrier X)}
    (f : M ⟶ N) : NonUnitalModuleHom (Carrier X) M.obj N.obj := f.hom

/-- Original module morphisms which also commute with the group actions. -/
structure Hom (M N : CompatibleTestAction.{uG, uX, uM} G X) where
  moduleHom : M.module ⟶ N.module
  comm : ∀ (g : G) (m : M.module.obj),
    moduleMap moduleHom (M.action g m) = N.action g (moduleMap moduleHom m)

@[ext]
theorem Hom.ext {M N : CompatibleTestAction.{uG, uX, uM} G X}
    {f g : Hom M N} (h : f.moduleHom = g.moduleHom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category (CompatibleTestAction.{uG, uX, uM} G X) where
  Hom := Hom
  id M := ⟨𝟙 M.module, fun _ _ => rfl⟩
  comp {M N P} f g := ⟨f.moduleHom ≫ g.moduleHom, fun k m => by
    change moduleMap g.moduleHom (moduleMap f.moduleHom (M.action k m)) =
      P.action k (moduleMap g.moduleHom (moduleMap f.moduleHom m))
    rw [f.comm, g.comm]⟩
  id_comp f := Hom.ext (Category.id_comp _)
  comp_id f := Hom.ext (Category.comp_id _)
  assoc f g h := Hom.ext (Category.assoc _ _ _)

variable (G X)

/-- Forget the compatible action, retaining the original nondegenerate test module. -/
def toTestModule :
    CompatibleTestAction.{uG, uX, uM} G X ⥤
      NondegenerateModuleCat.{uX, uM} (Carrier X) where
  obj M := M.module
  map {M N} (f : Hom M N) := f.moduleHom

end CompatibleTestAction

end Langlands.Sheaf.Renard.CompatibleTestActions
