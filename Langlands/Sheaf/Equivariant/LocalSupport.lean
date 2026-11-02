import Langlands.Sheaf.Equivariant.Topological
import Langlands.Sheaf.LocalSupport
import Mathlib.RepresentationTheory.Rep.Basic

/-! # Equivariant compact sections from actual local vanishing -/

noncomputable section

universe u v r w

namespace Langlands.Sheaf.Equivariant.LocalCompactSections

open CategoryTheory TopologicalSpace Opposite

variable {R : Type r} [CommRing R] {G : Type v} [Group G]
  {X : Type u} [TopologicalSpace X] [MulAction G X]
  (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{w} R)

/-- The actual ordinary-open restriction of the labelled presheaf. -/
abbrev ordinary : (TopCat.of X).Presheaf (ModuleCat.{w} R) :=
  (underlyingPresheaf G X (ModuleCat.{w} R)).obj F

/-- Ordinary restriction from the whole space to a labelled open object. -/
def restrict (U : ActionOpens G X) :
    F.obj (op ActionOpens.top) ⟶ F.obj (op U) :=
  F.map (ActionOpens.inclusionHom (U := U) (V := ActionOpens.top) le_top).op

@[simp]
theorem ordinary_restrict (U : Opens X) :
    Langlands.Sheaf.LocalSupport.restrict (ordinary F) U = restrict F ⟨U⟩ := rfl

/-- Local vanishing uses the original open restrictions. -/
theorem vanishesNear_iff (s : F.obj (op ActionOpens.top)) (x : X) :
    Langlands.Sheaf.LocalSupport.VanishesNear (ordinary F) s x ↔
      ∃ U : ActionOpens G X, x ∈ U.openSet ∧ restrict F U s = 0 := by
  constructor
  · rintro ⟨U, hxU, hU⟩
    exact ⟨⟨U⟩, hxU, hU⟩
  · rintro ⟨U, hxU, hU⟩
    exact ⟨U.openSet, hxU, hU⟩

/-- The original group action on global sections. -/
abbrev globalRepresentation : Representation R G (F.obj (op ActionOpens.top)) :=
  ((Rep.ActionToRep R G).obj (sectionAction F)).ρ

variable [ContinuousConstSMul G X]

/-- Ordinary restriction commutes with the actual translated section operator. -/
theorem restrict_action (g : G) (U : ActionOpens G X)
    (s : F.obj (op ActionOpens.top)) :
    restrict F (ActionOpens.translate g U) (globalRepresentation F g s) =
      F.map (ActionOpens.translationIso g U).inv.op (restrict F U s) := by
  let i : U ⟶ ActionOpens.top := ActionOpens.inclusionHom le_top
  let j : ActionOpens.translate g U ⟶ ActionOpens.top :=
    ActionOpens.inclusionHom le_top
  have h : (ActionOpens.sectionArrow g).op ≫ j.op =
      i.op ≫ (ActionOpens.translationIso g U).inv.op := by
    apply Quiver.Hom.unop_inj
    apply ActionOpens.Hom.ext
    simp [i, j, ActionOpens.inclusionHom, ActionOpens.sectionArrow,
      ActionOpens.translationIso]
  have hf := congrArg F.map h
  rw [F.map_comp, F.map_comp] at hf
  exact congrArg
    (fun f : F.obj (op ActionOpens.top) ⟶
      F.obj (op (ActionOpens.translate g U)) => f.hom s) hf

/-- A genuine vanishing neighborhood transports to the translated point. -/
theorem vanishesNear_action (g : G) (s : F.obj (op ActionOpens.top)) (x : X)
    (hx : Langlands.Sheaf.LocalSupport.VanishesNear (ordinary F) s (g⁻¹ • x)) :
    Langlands.Sheaf.LocalSupport.VanishesNear (ordinary F)
      (globalRepresentation F g s) x := by
  obtain ⟨U, hxU, hU⟩ := (vanishesNear_iff F s _).mp hx
  apply (vanishesNear_iff F _ x).mpr
  refine ⟨ActionOpens.translate g U, hxU, ?_⟩
  rw [restrict_action, hU, map_zero]

/-- Local vanishing is exactly transported, using the inverse group operator. -/
theorem vanishesNear_action_iff (g : G) (s : F.obj (op ActionOpens.top)) (x : X) :
    Langlands.Sheaf.LocalSupport.VanishesNear (ordinary F)
        (globalRepresentation F g s) x ↔
      Langlands.Sheaf.LocalSupport.VanishesNear (ordinary F) s (g⁻¹ • x) := by
  constructor
  · intro hx
    have h := vanishesNear_action F g⁻¹ (globalRepresentation F g s) (g⁻¹ • x)
      (by simpa using hx)
    simpa only [Representation.inv_self_apply] using h
  · exact vanishesNear_action F g s x

/-- The actual local support is exactly the spatial translate of the old support. -/
theorem support_action (g : G) (s : F.obj (op ActionOpens.top)) :
    Langlands.Sheaf.LocalSupport.support (ordinary F) (globalRepresentation F g s) =
      (fun x : X => g • x) '' Langlands.Sheaf.LocalSupport.support (ordinary F) s := by
  ext x
  constructor
  · intro hx
    exact ⟨g⁻¹ • x, fun hz => hx ((vanishesNear_action_iff F g s x).mpr hz),
      smul_inv_smul g x⟩
  · rintro ⟨y, hy, rfl⟩ hz
    exact hy (by simpa using (vanishesNear_action_iff F g s (g • y)).mp hz)

/-- Each group operator preserves the entire compact-support submodule. -/
theorem preserves_compactSupport (g : G) (s : F.obj (op ActionOpens.top))
    (hs : IsCompact (Langlands.Sheaf.LocalSupport.support (ordinary F) s)) :
    IsCompact (Langlands.Sheaf.LocalSupport.support (ordinary F)
      (globalRepresentation F g s)) := by
  rw [support_action]
  exact hs.image (continuous_const_smul g)

/-- Restrict the original group operators to all compactly supported sections. -/
def representation :
    Representation R G (Langlands.Sheaf.LocalSupport.submodule (ordinary F)) :=
  (globalRepresentation F).subrepresentation
    (Langlands.Sheaf.LocalSupport.submodule (ordinary F))
    (fun g s hs => preserves_compactSupport F g s hs)

@[simp]
theorem representation_apply (g : G)
    (s : Langlands.Sheaf.LocalSupport.submodule (ordinary F)) :
    (representation F g s).val = globalRepresentation F g s.val := rfl

variable {F}

/-- Naturality on labelled arrows gives the actual compact-section intertwiner. -/
def map {F' : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{w} R} (f : F ⟶ F') :
    (representation F).IntertwiningMap (representation F') where
  toLinearMap := Langlands.Sheaf.LocalSupport.map
    ((underlyingPresheaf G X (ModuleCat.{w} R)).map f)
  isIntertwining' g := by
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    exact congrArg
      (fun k : F.obj (op ActionOpens.top) ⟶
        F'.obj (op ActionOpens.top) => k.hom s.val)
      (f.naturality (ActionOpens.sectionArrow g).op)

variable (R G X)

/-- Global-section representations with independent space and module universes. -/
def globalFunctor : TopologicalSheaf G X (ModuleCat.{w} R) ⥤ Rep.{w} R G :=
  sections G X (ModuleCat.{w} R) ⋙ Rep.ActionToRep R G

/-- Compact sections are functorial even before the sheaf condition is imposed. -/
def presheafFunctor :
    ((ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{w} R) ⥤ Rep.{w} R G where
  obj F := Rep.of (representation F)
  map f := Rep.ofHom (map f)
  map_id _ := by ext s; rfl
  map_comp _ _ := by ext s; rfl

/-- The compact-section functor on the full moving-space sheaf category. -/
def functor : TopologicalSheaf G X (ModuleCat.{w} R) ⥤ Rep.{w} R G :=
  toTransportPresheaf G X (ModuleCat.{w} R) ⋙ presheafFunctor R G X

/-- The natural equivariant inclusion is the original global-section inclusion. -/
def inclusion : functor R G X ⟶ globalFunctor R G X where
  app F := Rep.ofHom
    { toLinearMap := (Langlands.Sheaf.LocalSupport.submodule (ordinary F.obj)).subtype
      isIntertwining' _ := rfl }
  naturality _ _ _ := by ext s; rfl

end Langlands.Sheaf.Equivariant.LocalCompactSections
