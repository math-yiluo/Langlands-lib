import Langlands.Sheaf.Renard.GermSupportClosedness

/-!
# Compactly supported germ-section groups and induced maps

The group carrier is the existing literal compact-support subtype.
Closedness is used in the actual domain, with no separation hypothesis.
-/

noncomputable section

open CategoryTheory TopologicalSpace

universe u v

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X] {B : OpenBasis X}

/-- Compact supports are closed under addition because the sum support is
relatively closed inside the compact union of the two supports. -/
theorem isCompact_germSupport_add {F : RawPresheaf.{u,v} B} {U : Opens X}
    {s t : GermSections F U} (hs : IsCompact (germSupport s))
    (ht : IsCompact (germSupport t)) : IsCompact (germSupport (s + t)) :=
  (hs.union ht).of_isClosed_subset
    (rawGermRelativeSupportClosedness F U (s + t)) (germSupport_add_subset s t)

/-- The subgroup carrier is exactly the previously defined compact-section set. -/
def compactGermSectionSubgroup (F : RawPresheaf.{u,v} B) (U : Opens X) :
    AddSubgroup (GermSections F U) where
  carrier := compactGermSectionsSet F U
  zero_mem' := zero_mem_compactGermSectionsSet F U
  add_mem' := isCompact_germSupport_add
  neg_mem' := by
    intro s hs
    change IsCompact (germSupport s) at hs
    change IsCompact (germSupport (-s))
    simpa only [germSupport_neg] using hs

@[simp]
theorem compactGermSectionSubgroup_carrier (F : RawPresheaf.{u,v} B) (U : Opens X) :
    (compactGermSectionSubgroup F U : Set (GermSections F U)) =
      compactGermSectionsSet F U := rfl

@[simp]
theorem mem_compactGermSectionSubgroup (F : RawPresheaf.{u,v} B) (U : Opens X)
    (s : GermSections F U) :
    s ∈ compactGermSectionSubgroup F U ↔ IsCompact (germSupport s) := Iff.rfl

theorem mem_compactGermSectionSubgroup_iff_ambient
    (F : RawPresheaf.{u,v} B) (U : Opens X) (s : GermSections F U) :
    s ∈ compactGermSectionSubgroup F U ↔ IsCompact (germSupportAmbient s) :=
  isCompact_germSupport_iff s

/-- Install the inherited group on the unchanged published set subtype. -/
instance compactGermSectionsAddCommGroup (F : RawPresheaf.{u,v} B) (U : Opens X) :
    AddCommGroup (CompactGermSections F U) :=
  inferInstanceAs (AddCommGroup ↥(compactGermSectionSubgroup F U))

@[ext]
theorem CompactGermSections.ext {F : RawPresheaf.{u,v} B} {U : Opens X}
    {s t : CompactGermSections F U}
    (h : ∀ x : U, s.val.val x = t.val.val x) : s = t :=
  Subtype.ext (GermSections.ext h)

@[simp]
theorem compactGermSections_coe_zero (F : RawPresheaf.{u,v} B) (U : Opens X) :
    ((0 : CompactGermSections F U) : GermSections F U) = 0 := rfl

@[simp]
theorem compactGermSections_coe_add {F : RawPresheaf.{u,v} B} {U : Opens X}
    (s t : CompactGermSections F U) :
    ((s + t : CompactGermSections F U) : GermSections F U) = s.val + t.val := rfl

@[simp]
theorem compactGermSections_coe_neg {F : RawPresheaf.{u,v} B} {U : Opens X}
    (s : CompactGermSections F U) :
    ((-s : CompactGermSections F U) : GermSections F U) = -s.val := rfl

@[simp]
theorem compactGermSections_zero_apply (F : RawPresheaf.{u,v} B) (U : Opens X) (x : U) :
    (0 : CompactGermSections F U).val.val x = 0 := rfl

@[simp]
theorem compactGermSections_add_apply {F : RawPresheaf.{u,v} B} {U : Opens X}
    (s t : CompactGermSections F U) (x : U) :
    (s + t).val.val x = s.val.val x + t.val.val x := rfl

@[simp]
theorem compactGermSections_neg_apply {F : RawPresheaf.{u,v} B} {U : Opens X}
    (s : CompactGermSections F U) (x : U) :
    (-s).val.val x = -s.val.val x := rfl

/-- Bundle the existing forgetful function, without changing its values. -/
def compactGermSectionsInclusionHom (F : RawPresheaf.{u,v} B) (U : Opens X) :
    CompactGermSections F U →+ GermSections F U where
  toFun := compactGermSectionsInclusion F U
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem compactGermSectionsInclusionHom_toFun (F : RawPresheaf.{u,v} B) (U : Opens X) :
    (compactGermSectionsInclusionHom F U : CompactGermSections F U → GermSections F U) =
      compactGermSectionsInclusion F U := rfl

@[simp]
theorem compactGermSectionsInclusionHom_apply (F : RawPresheaf.{u,v} B) (U : Opens X)
    (s : CompactGermSections F U) :
    compactGermSectionsInclusionHom F U s = s.val := rfl

@[simp]
theorem compactGermSectionsInclusionHom_apply_value
    (F : RawPresheaf.{u,v} B) (U : Opens X) (s : CompactGermSections F U) (x : U) :
    (compactGermSectionsInclusionHom F U s).val x = s.val.val x := rfl

theorem compactGermSectionsInclusionHom_injective
    (F : RawPresheaf.{u,v} B) (U : Opens X) :
    Function.Injective (compactGermSectionsInclusionHom F U) :=
  compactGermSectionsInclusion_injective F U

instance compactGermSections_empty_subsingleton (F : RawPresheaf.{u,v} B) :
    Subsingleton (CompactGermSections F (⊥ : Opens X)) :=
  ⟨fun _ _ => Subtype.ext (Subsingleton.elim _ _)⟩

instance compactGermSections_isEmpty_subsingleton [IsEmpty X]
    (F : RawPresheaf.{u,v} B) (U : Opens X) :
    Subsingleton (CompactGermSections F U) :=
  ⟨fun _ _ => CompactGermSections.ext
    (fun x => False.elim (isEmptyElim x.val : False))⟩

theorem compactGermSections_empty_eq_zero (F : RawPresheaf.{u,v} B)
    (s : CompactGermSections F (⊥ : Opens X)) : s = 0 :=
  Subsingleton.elim _ _

/-- The target support is closed inside the compact source support. -/
theorem isCompact_germSupport_map {F G : RawPresheaf.{u,v} B}
    (φ : F ⟶ G) (U : Opens X) {s : GermSections F U}
    (hs : IsCompact (germSupport s)) :
    IsCompact (germSupport (germSectionsMap φ U s)) :=
  hs.of_isClosed_subset (rawGermRelativeSupportClosedness G U (germSectionsMap φ U s))
    (germSupport_map_subset φ U s)

/-- An actual presheaf morphism acts on compact sections by its existing germ map. -/
def compactGermSectionsMap {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G)
    (U : Opens X) : CompactGermSections F U →+ CompactGermSections G U where
  toFun s := ⟨germSectionsMap φ U s.val, isCompact_germSupport_map φ U s.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' s t := Subtype.ext (map_add _ s.val t.val)

@[simp]
theorem compactGermSectionsMap_coe {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G)
    (U : Opens X) (s : CompactGermSections F U) :
    (compactGermSectionsMap φ U s).val = germSectionsMap φ U s.val := rfl

@[simp]
theorem compactGermSectionsMap_apply {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G)
    (U : Opens X) (s : CompactGermSections F U) (x : U) :
    (compactGermSectionsMap φ U s).val.val x =
      rawStalkMap φ x.val (s.val.val x) := rfl

theorem compactGermSectionsMap_inclusion {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G)
    (U : Opens X) :
    (compactGermSectionsInclusionHom G U).comp (compactGermSectionsMap φ U) =
      (germSectionsMap φ U).comp (compactGermSectionsInclusionHom F U) := rfl

@[simp]
theorem compactGermSectionsMap_zero {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G)
    (U : Opens X) :
    compactGermSectionsMap φ U 0 = 0 :=
  map_zero _

theorem compactGermSectionsMap_add {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G)
    (U : Opens X) (s t : CompactGermSections F U) :
    compactGermSectionsMap φ U (s + t) =
      compactGermSectionsMap φ U s + compactGermSectionsMap φ U t :=
  map_add _ _ _

@[simp]
theorem compactGermSectionsMap_id (F : RawPresheaf.{u,v} B) (U : Opens X) :
    compactGermSectionsMap (𝟙 F) U = AddMonoidHom.id (CompactGermSections F U) := by
  apply AddMonoidHom.ext
  intro s
  apply Subtype.ext
  exact DFunLike.congr_fun (germSectionsMap_id F U) s.val

theorem compactGermSectionsMap_comp {F G H : RawPresheaf.{u,v} B}
    (φ : F ⟶ G) (ψ : G ⟶ H) (U : Opens X) :
    compactGermSectionsMap (φ ≫ ψ) U =
      (compactGermSectionsMap ψ U).comp (compactGermSectionsMap φ U) := by
  apply AddMonoidHom.ext
  intro s
  apply Subtype.ext
  exact DFunLike.congr_fun (germSectionsMap_comp φ ψ U) s.val

end Langlands.Sheaf.Renard
