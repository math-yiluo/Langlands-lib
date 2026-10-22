import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Sections and their local trivialization locus -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.SchemeModule

variable {X : Scheme.{u}} (M : X.Modules)

/-- Global sections of an actual sheaf of modules on a scheme. -/
noncomputable abbrev GlobalSections := Γ(M, ⊤)

/-- The structure sheaf, viewed as a module over itself. -/
noncomputable def structureModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The compatible family of restrictions determined by a global section. -/
noncomputable def sectionFamily (s : GlobalSections M) : M.sections :=
  M.val.sectionsMk
    (fun U ↦ M.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s)
    (by
      intro U V f
      change M.presheaf.map f (M.presheaf.map _ s) = M.presheaf.map _ s
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)

/-- The morphism from the structure module taking one to the specified section. -/
noncomputable def sectionHom (s : GlobalSections M) : structureModule X ⟶ M :=
  M.unitHomEquiv.symm (sectionFamily M s)

/-- The section trivializes the module on the specified open subscheme. -/
def TrivializesOn (s : GlobalSections M) (U : X.Opens) : Prop :=
  IsIso ((Scheme.Modules.restrictFunctor U.ι).map (sectionHom M s))

/-- The union of all open subschemes on which the section is a trivialization. -/
def trivializationOpen (s : GlobalSections M) : X.Opens :=
  sSup {U | TrivializesOn M s U}

/-- The actual open subscheme of the local trivialization locus. -/
def trivializationSubscheme (s : GlobalSections M) : Scheme.{u} :=
  (trivializationOpen M s).toScheme

/-- The canonical open immersion from the local trivialization locus. -/
def trivializationInclusion (s : GlobalSections M) :
    trivializationSubscheme M s ⟶ X :=
  (trivializationOpen M s).ι

/-- A pointwise condition: the section's morphism is an isomorphism on the stalk. -/
def IsStalkFrame (s : GlobalSections M) (x : X) : Prop :=
  IsIso ((TopCat.Presheaf.stalkFunctor Ab x).map
    ((Scheme.Modules.toPresheaf X).map (sectionHom M s)))

end Langlands.SchemeModule
