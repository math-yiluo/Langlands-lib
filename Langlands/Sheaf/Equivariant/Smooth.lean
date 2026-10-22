import Langlands.Sheaf.Equivariant.Limits
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Smooth equivariant sheaves

For a topological group acting on a space, an equivariant module sheaf is
smooth when every section is, near every point, fixed by an open subgroup
stabilizing a neighbourhood of that point.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory CategoryTheory.Limits Opposite

universe u uG

variable (R : Type u) [CommRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {X : Type u} [TopologicalSpace X] [MulAction G X]

/-- Near `x`, the section `s` over `U` restricts to a section over a smaller
neighbourhood that is stable under, and fixed by, an open subgroup. -/
def IsLocallyFixedAt (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R) {U : ActionOpens G X}
    (s : F.obj (op U)) (x : X) : Prop :=
  ∃ (V : ActionOpens G X) (hVU : V.openSet ≤ U.openSet) (H : OpenSubgroup G)
    (hV : ∀ h : (H : Subgroup G), ∀ y ∈ V.openSet, (h : G) • y ∈ V.openSet),
    x ∈ V.openSet ∧ ∀ h : (H : Subgroup G),
      (F.map (ActionOpens.invariantArrow (H : Subgroup G) V hV h).op).hom
          ((F.map (ActionOpens.inclusionHom hVU).op).hom s) =
        (F.map (ActionOpens.inclusionHom hVU).op).hom s

variable (G X)

/-- An equivariant module sheaf is smooth when every section is locally fixed
by open subgroups at every point of its open. -/
def IsSmoothSheaf (F : TopologicalSheaf G X (ModuleCat.{u} R)) : Prop :=
  ∀ (U : ActionOpens G X) (s : F.obj.obj (op U)) (x : X), x ∈ U.openSet →
    IsLocallyFixedAt R F.obj s x

/-- The property of being a smooth equivariant module sheaf. -/
def smoothSheafProperty : ObjectProperty (TopologicalSheaf G X (ModuleCat.{u} R)) :=
  fun F => IsSmoothSheaf R G X F

/-- The full subcategory of smooth equivariant module sheaves. -/
abbrev SmoothTopologicalSheaf := (smoothSheafProperty R G X).FullSubcategory

/-- The inclusion of smooth equivariant module sheaves. -/
def smoothInclusion : SmoothTopologicalSheaf R G X ⥤ TopologicalSheaf G X (ModuleCat.{u} R) :=
  (smoothSheafProperty R G X).ι

variable {G X}

/-- For a discrete group every equivariant module sheaf is smooth. -/
theorem isSmoothSheaf_of_discreteTopology [DiscreteTopology G]
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) : IsSmoothSheaf R G X F := by
  intro U s x hx
  refine ⟨U, le_rfl, ⟨⊥, isOpen_discrete _⟩, ?_, hx, ?_⟩
  · rintro ⟨h, hh⟩ y hy
    rw [Subgroup.mem_bot] at hh
    subst hh
    simpa using hy
  · rintro ⟨h, hh⟩
    rw [Subgroup.mem_bot] at hh
    subst hh
    rw [← ModuleCat.comp_apply, ← F.obj.map_comp]
    have key : ∀ f g : op U ⟶ op U, f = g → (F.obj.map f).hom s = (F.obj.map g).hom s :=
      fun f g hfg => by rw [hfg]
    apply key
    apply Quiver.Hom.unop_inj
    apply ActionOpens.Hom.ext
    simp [ActionOpens.invariantArrow, ActionOpens.inclusionHom]

/-- A subsheaf of a smooth equivariant module sheaf is smooth. -/
theorem IsSmoothSheaf.of_mono {F F' : TopologicalSheaf G X (ModuleCat.{u} R)} (f : F ⟶ F')
    [Mono f] (hF' : IsSmoothSheaf R G X F') : IsSmoothSheaf R G X F := by
  intro U s x hx
  obtain ⟨V, hVU, H, hV, hxV, hfix⟩ := hF' U ((f.hom.app (op U)).hom s) x hx
  refine ⟨V, hVU, H, hV, hxV, fun h => ?_⟩
  have hinj : Function.Injective (f.hom.app (op V)).hom := by
    have : Mono ((evaluation G X (ModuleCat.{u} R) V).map f) := inferInstance
    exact (ModuleCat.mono_iff_injective _).1 this
  apply hinj
  have h1 := congrArg (fun k => k.hom s)
    (f.hom.naturality ((ActionOpens.inclusionHom hVU).op ≫
      (ActionOpens.invariantArrow (H : Subgroup G) V hV h).op))
  have h2 := congrArg (fun k => k.hom s) (f.hom.naturality (ActionOpens.inclusionHom hVU).op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, CategoryTheory.Functor.map_comp] at h1 h2
  rw [h1, h2]
  exact hfix h

end Langlands.Sheaf.Equivariant
