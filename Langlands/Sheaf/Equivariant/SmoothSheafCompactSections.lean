import Langlands.Sheaf.Equivariant.SmoothAbelian
import Langlands.Sheaf.Equivariant.CompactSupport
import Langlands.Cohomology.EquivariantDerivedSections
import Langlands.Representation.Category.Abelian
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Compactly supported sections of smooth equivariant sheaves

Every compactly supported global section of a smooth equivariant module sheaf
is fixed by an open subgroup. Compact sections of smooth sheaves therefore form
a functor from smooth equivariant module sheaves to smooth representations,
and this functor is left exact.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u uG

namespace CompactSections

section Fixed

variable {R : Type u} [CommRing R]
variable {G : Type uG} [Group G]
variable {X : Type u} [TopologicalSpace X] [MulAction G X]

/-- On an open stable under a subgroup `H`, if `H` fixes the restriction of a
global section, then the translate of the section by an element of `H` has the
same restriction. -/
theorem restrict_sectionAction_eq (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R)
    {s : F.obj (op ActionOpens.top)} {V : ActionOpens G X}
    (hVU : V.openSet ≤ (ActionOpens.top : ActionOpens G X).openSet) (H : Subgroup G)
    (hV : ∀ h : H, ∀ y ∈ V.openSet, (h : G) • y ∈ V.openSet)
    (hfix : ∀ h : H, (F.map (ActionOpens.invariantArrow H V hV h).op).hom
        ((F.map (ActionOpens.inclusionHom hVU).op).hom s) =
      (F.map (ActionOpens.inclusionHom hVU).op).hom s) (h : H) :
    restrict F V (((sectionAction F).ρ (h : G)).hom s) = restrict F V s := by
  have e : ActionOpens.invariantArrow H V hV h ≫ ActionOpens.inclusionHom hVU =
      ActionOpens.inclusionHom hVU ≫ ActionOpens.sectionArrow (h : G) := by
    apply ActionOpens.Hom.ext
    simp [ActionOpens.invariantArrow, ActionOpens.inclusionHom, ActionOpens.sectionArrow]
  have key := congrArg (fun k => (F.map k.op).hom s) e
  simp only [op_comp, CategoryTheory.Functor.map_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply] at key
  rw [hfix h] at key
  exact key.symm

variable [TopologicalSpace G] [ContinuousConstSMul G X]

/-- Every compactly supported global section of a smooth equivariant module
sheaf is fixed by an open subgroup. By compactness the support is covered by
finitely many neighbourhoods, each stable under and fixing the section for some
open subgroup. The intersection of these subgroups fixes every germ: inside the
union of the neighbourhoods the translate agrees with the section, and outside
it both the section and its translate have zero germs. -/
theorem isSmooth_representation_of_isSmoothSheaf
    {F : TopologicalSheaf G X (ModuleCat.{u} R)} (hF : IsSmoothSheaf R G X F) :
    Langlands.IsSmooth (representation F.obj) := by
  rintro ⟨s, hs⟩
  change IsCompact (Langlands.Sheaf.CompactSupport.support (ordinary F.obj) s) at hs
  let germEq : G → X → Prop := fun h y =>
    (ordinary F.obj).Γgerm y (((sectionAction F.obj).ρ h).hom s) =
      (ordinary F.obj).Γgerm y s
  let p : Set X → Prop := fun S => ∃ (H : OpenSubgroup G) (W : Set X), S ⊆ W ∧
    (∀ h ∈ H, ∀ y ∈ W, h • y ∈ W) ∧ ∀ h ∈ H, ∀ y ∈ W, germEq h y
  have hp : p (Langlands.Sheaf.CompactSupport.support (ordinary F.obj) s) := by
    refine hs.induction_on ?_ ?_ ?_ ?_
    · exact ⟨⊤, ∅, subset_rfl, fun _ _ _ hy => hy, fun _ _ _ hy => absurd hy id⟩
    · rintro S T hST ⟨H, W, hTW, hstab, hgerm⟩
      exact ⟨H, W, hST.trans hTW, hstab, hgerm⟩
    · rintro S T ⟨H₁, W₁, hS, hstab₁, hgerm₁⟩ ⟨H₂, W₂, hT, hstab₂, hgerm₂⟩
      refine ⟨H₁ ⊓ H₂, W₁ ∪ W₂, Set.union_subset_union hS hT, ?_, ?_⟩
      · rintro h hh y (hy | hy)
        · exact Or.inl (hstab₁ h (OpenSubgroup.mem_inf.1 hh).1 y hy)
        · exact Or.inr (hstab₂ h (OpenSubgroup.mem_inf.1 hh).2 y hy)
      · rintro h hh y (hy | hy)
        · exact hgerm₁ h (OpenSubgroup.mem_inf.1 hh).1 y hy
        · exact hgerm₂ h (OpenSubgroup.mem_inf.1 hh).2 y hy
    · intro x _
      obtain ⟨V, hVU, H, hV, hxV, hfix⟩ := hF ActionOpens.top s x trivial
      refine ⟨V.openSet, mem_nhdsWithin_of_mem_nhds (V.openSet.isOpen.mem_nhds hxV),
        H, V.openSet, subset_rfl, fun h hh y hy => hV ⟨h, hh⟩ y hy, fun h hh y hy => ?_⟩
      have hres := restrict_sectionAction_eq F.obj hVU (H : Subgroup G) hV hfix ⟨h, hh⟩
      change (ordinary F.obj).Γgerm y (((sectionAction F.obj).ρ h).hom s) =
        (ordinary F.obj).Γgerm y s
      rw [← (ordinary F.obj).Γgerm_res_apply y hy (((sectionAction F.obj).ρ h).hom s)
          (i := homOfLE (show V.openSet ≤ ⊤ from le_top)),
        ← (ordinary F.obj).Γgerm_res_apply y hy s
          (i := homOfLE (show V.openSet ≤ ⊤ from le_top))]
      change (ordinary F.obj).germ V.openSet y hy
          (restrict F.obj V (((sectionAction F.obj).ρ h).hom s)) =
        (ordinary F.obj).germ V.openSet y hy (restrict F.obj V s)
      rw [hres]
  obtain ⟨H, W, hKW, hstab, hgerm⟩ := hp
  refine ⟨H, (Representation.mem_invariants _ _).2 fun h => ?_⟩
  apply Subtype.ext
  change ((sectionAction F.obj).ρ (h : G)).hom s = s
  apply TopCat.Presheaf.section_ext ((toSheaf G X (ModuleCat.{u} R)).obj F) ⊤
  intro y _
  change (ordinary F.obj).Γgerm y (((sectionAction F.obj).ρ (h : G)).hom s) =
    (ordinary F.obj).Γgerm y s
  by_cases hy : y ∈ W
  · exact hgerm h h.2 y hy
  · have hs0 : (ordinary F.obj).Γgerm y s = 0 := by
      by_contra hne
      exact hy (hKW hne)
    have hhs0 : (ordinary F.obj).Γgerm y (((sectionAction F.obj).ρ (h : G)).hom s) = 0 := by
      by_contra hne
      obtain ⟨k, hk, rfl⟩ := support_action_subset F.obj (h : G) s hne
      exact hy (hstab h h.2 k (hKW hk))
    rw [hs0, hhs0]

end Fixed

end CompactSections

section Functor

variable (R : Type u) [CommRing R]
variable (G : Type uG) [Group G] [TopologicalSpace G]
variable (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

/-- Compactly supported sections of smooth equivariant module sheaves, as
smooth representations. -/
def smoothSheafCompactSections :
    SmoothTopologicalSheaf R G X ⥤ Langlands.SmoothRep.{u, uG, u} R G :=
  (Langlands.smoothRepProperty R G).lift (smoothInclusion R G X ⋙ CompactSections.functor R G X)
    fun F => CompactSections.isSmooth_representation_of_isSmoothSheaf F.property

/-- The representation underlying the smooth compact sections of a smooth sheaf
is its compact section representation. -/
def smoothSheafCompactSectionsToRepIso :
    smoothSheafCompactSections R G X ⋙ Langlands.SmoothRep.toRep ≅
      smoothInclusion R G X ⋙ CompactSections.functor R G X :=
  ObjectProperty.liftCompιIso _ _ _

end Functor

section LeftExact

variable (R : Type u) [CommRing R]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable [HasStableNeighbourhoods G X]

/-- The inclusion of smooth equivariant module sheaves is left exact. -/
instance smoothInclusion_preservesFiniteLimits :
    PreservesFiniteLimits (smoothInclusion R G X) := by
  have : ∀ {A B : SmoothTopologicalSheaf R G X} (f : A ⟶ B),
      PreservesLimit (parallelPair f 0) (smoothInclusion R G X) :=
    fun f => (smoothSheafProperty R G X).preservesKernels_ι f
  exact Functor.preservesFiniteLimits_of_preservesKernels _

instance smoothInclusion_additive : (smoothInclusion R G X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Compact sections of smooth sheaves are left exact as a functor to smooth
representations. -/
instance smoothSheafCompactSections_preservesFiniteLimits :
    PreservesFiniteLimits (smoothSheafCompactSections R G X) := by
  have : PreservesFiniteLimits (smoothInclusion R G X ⋙ CompactSections.functor R G X) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (smoothSheafCompactSections R G X ⋙ Langlands.SmoothRep.toRep) :=
    preservesFiniteLimits_of_natIso (smoothSheafCompactSectionsToRepIso R G X).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ Langlands.SmoothRep.toRep

instance smoothSheafCompactSections_additive : (smoothSheafCompactSections R G X).Additive :=
  Functor.additive_of_preserves_binary_products _

end LeftExact

end Langlands.Sheaf.Equivariant
