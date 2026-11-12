import Langlands.Sheaf.Equivariant.SmoothCompactSupport
import Langlands.Sheaf.Equivariant.Smooth
import Mathlib.Basic.Complex.Basic

/-!
# Renard's smooth actions on complex vector sheaves

The underlying equivariant sheaves and compact-section representations are
the published transport-category constructions. Renard's smoothness condition
is imposed on the entire compact-section representation.
-/

noncomputable section

namespace Langlands.Sheaf.Renard.SectionActions

open CategoryTheory Opposite
open Langlands.Sheaf.Equivariant

universe uG

variable (G : Type uG) [Group G] [TopologicalSpace G]
variable (X : Type) [TopologicalSpace X] [MulAction G X]

/-- A complex vector sheaf with an action covering the fixed action on `X`.
In Renard's setting the fixed action is jointly continuous. -/
abbrev ActionSheaf := TopologicalSheaf G X (ModuleCat.{0} ℂ)

variable {G X}

/-- The ordinary complex vector sheaf, with the action forgotten. -/
abbrev underlying (F : ActionSheaf G X) :=
  (toSheaf G X (ModuleCat.{0} ℂ)).obj F

/-- The published representation on all global sections. -/
abbrev globalRepresentation (F : ActionSheaf G X) :=
  CompactSections.globalRepresentation F.obj

omit [TopologicalSpace G] in
theorem global_one (F : ActionSheaf G X) (s : F.obj.obj (op ActionOpens.top)) :
    globalRepresentation F 1 s = s :=
  LinearMap.congr_fun (map_one (globalRepresentation F)) s

omit [TopologicalSpace G] in
theorem global_mul (F : ActionSheaf G X) (g h : G)
    (s : F.obj.obj (op ActionOpens.top)) :
    globalRepresentation F (g * h) s =
      globalRepresentation F g (globalRepresentation F h s) :=
  LinearMap.congr_fun (map_mul (globalRepresentation F) g h) s

section ContinuousAction

variable [ContinuousSMul G X]

/-- Renard's isomorphism on sections over a translated open. -/
abbrev gamma (F : ActionSheaf G X) (g : G) (U : ActionOpens G X) :=
  translateSections F g U

/-- Renard's representation on all compactly supported global sections. -/
abbrev compactRepresentation (F : ActionSheaf G X) :=
  CompactSections.representation F.obj

/-- Renard III.3.1: smoothness of the entire compact-section representation. -/
def IsSmoothAction (F : ActionSheaf G X) : Prop :=
  Langlands.IsSmooth (compactRepresentation F)

/-- The algebraic dual of the actual compact-section space. -/
abbrev Distribution (F : ActionSheaf G X) :=
  Module.Dual ℂ
    (Langlands.Sheaf.CompactSupport.submodule (CompactSections.ordinary F.obj))

/-- Invariance under the dual action, equivalently invariance on translated tests. -/
def IsInvariantDistribution (F : ActionSheaf G X) (T : Distribution F) : Prop :=
  ∀ (g : G) (s : Langlands.Sheaf.CompactSupport.submodule
    (CompactSections.ordinary F.obj)), T (compactRepresentation F g s) = T s

/-- The subspace of invariant algebraic distributions. -/
def invariantDistributions (F : ActionSheaf G X) : Submodule ℂ (Distribution F) where
  carrier := {T | IsInvariantDistribution F T}
  zero_mem' := by intro g s; rfl
  add_mem' := by
    intro T S hT hS g s
    change T (compactRepresentation F g s) + S (compactRepresentation F g s) =
      T s + S s
    rw [hT g s, hS g s]
  smul_mem' := by
    intro c T hT g s
    change c • T (compactRepresentation F g s) = c • T s
    rw [hT g s]

@[simp]
theorem mem_invariantDistributions (F : ActionSheaf G X) (T : Distribution F) :
    T ∈ invariantDistributions F ↔ IsInvariantDistribution F T := Iff.rfl

variable (G X)

/-- The property used in Renard's category of smooth action sheaves. -/
def smoothActionProperty : ObjectProperty (ActionSheaf G X) :=
  IsSmoothAction

/-- Renard's category, with the published equivariant sheaf morphisms. -/
abbrev SmoothActionSheaf := (smoothActionProperty G X).FullSubcategory

/-- Forget only Renard's compact-section smoothness condition. -/
def smoothActionInclusion : SmoothActionSheaf G X ⥤ ActionSheaf G X :=
  (smoothActionProperty G X).ι

/-- The functor `Γ_c` uses every compact section. -/
def gammaC : SmoothActionSheaf G X ⥤ Langlands.SmoothRep.{0, uG, 0} ℂ G :=
  (Langlands.smoothRepProperty ℂ G).lift
    (smoothActionInclusion G X ⋙ CompactSections.functor ℂ G X)
    (fun F => F.property)

/-- Forgetting smoothness recovers the published compact-section functor. -/
def gammaCToRepIso :
    gammaC G X ⋙ Langlands.SmoothRep.toRep ≅
      smoothActionInclusion G X ⋙ CompactSections.functor ℂ G X :=
  (Langlands.smoothRepProperty ℂ G).liftCompιIso
    (smoothActionInclusion G X ⋙ CompactSections.functor ℂ G X)
    (fun F => F.property)

variable {G X}

/-- The object assigned by `Γ_c` has exactly the original compact-section action. -/
theorem gammaC_representation (F : SmoothActionSheaf G X) :
    ((gammaC G X).obj F).representation = compactRepresentation F.obj := rfl

/-- The map assigned by `Γ_c` is the original restriction of the sheaf map. -/
theorem gammaC_map {F F' : SmoothActionSheaf G X} (f : F ⟶ F') :
    Langlands.SmoothRep.hom ((gammaC G X).map f) =
      CompactSections.map f.hom := rfl

end ContinuousAction

end Langlands.Sheaf.Renard.SectionActions
