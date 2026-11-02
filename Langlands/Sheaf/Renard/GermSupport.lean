import Langlands.Sheaf.Renard.GermSections
import Mathlib.Topology.Compactness.Compact

/-!
# Supports and compact-section carriers for locally represented germs

Support is the literal nonzero set in the domain subtype. Its ambient image
and compactness are exposed separately, without any separation hypothesis.
-/

noncomputable section

open CategoryTheory TopologicalSpace

universe u v

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X] {B : OpenBasis X}

/-- The relative support is the nonzero set itself, without taking a closure. -/
def germSupport {F : RawPresheaf.{u,v} B} {U : Opens X}
    (s : GermSections F U) : Set U :=
  {x | s.val x ≠ 0}

/-- The same support viewed in the ambient space by the actual subtype inclusion. -/
def germSupportAmbient {F : RawPresheaf.{u,v} B} {U : Opens X}
    (s : GermSections F U) : Set X :=
  (Subtype.val : U → X) '' germSupport s

@[simp]
theorem mem_germSupport {F : RawPresheaf.{u,v} B} {U : Opens X}
    (s : GermSections F U) (x : U) :
    x ∈ germSupport s ↔ s.val x ≠ 0 := Iff.rfl

theorem germSupportAmbient_eq_image {F : RawPresheaf.{u,v} B} {U : Opens X}
    (s : GermSections F U) :
    germSupportAmbient s = (Subtype.val : U → X) '' germSupport s := rfl

@[simp]
theorem mem_germSupportAmbient {F : RawPresheaf.{u,v} B} {U : Opens X}
    (s : GermSections F U) (x : X) :
    x ∈ germSupportAmbient s ↔ ∃ hx : x ∈ U, s.val ⟨x, hx⟩ ≠ 0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hx, hs⟩
    exact ⟨⟨x, hx⟩, hs, rfl⟩

theorem germSupportAmbient_subset {F : RawPresheaf.{u,v} B} {U : Opens X}
    (s : GermSections F U) : germSupportAmbient s ⊆ (U : Set X) := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

@[simp]
theorem germSupport_zero (F : RawPresheaf.{u,v} B) (U : Opens X) :
    germSupport (0 : GermSections F U) = ∅ := by
  ext x
  simp [germSupport]

@[simp]
theorem germSupportAmbient_zero (F : RawPresheaf.{u,v} B) (U : Opens X) :
    germSupportAmbient (0 : GermSections F U) = ∅ := by
  simp [germSupportAmbient]

@[simp]
theorem germSupport_neg {F : RawPresheaf.{u,v} B} {U : Opens X}
    (s : GermSections F U) : germSupport (-s) = germSupport s := by
  ext x
  simp [germSupport]

@[simp]
theorem germSupportAmbient_neg {F : RawPresheaf.{u,v} B} {U : Opens X}
    (s : GermSections F U) : germSupportAmbient (-s) = germSupportAmbient s := by
  simp [germSupportAmbient]

theorem germSupport_add_subset {F : RawPresheaf.{u,v} B} {U : Opens X}
    (s t : GermSections F U) :
    germSupport (s + t) ⊆ germSupport s ∪ germSupport t := by
  intro x hx
  change s.val x + t.val x ≠ 0 at hx
  change s.val x ≠ 0 ∨ t.val x ≠ 0
  by_cases hs : s.val x = 0
  · exact Or.inr (by simpa [hs] using hx)
  · exact Or.inl hs

theorem germSupportAmbient_add_subset {F : RawPresheaf.{u,v} B} {U : Opens X}
    (s t : GermSections F U) :
    germSupportAmbient (s + t) ⊆ germSupportAmbient s ∪ germSupportAmbient t := by
  rintro _ ⟨x, hx, rfl⟩
  rcases germSupport_add_subset s t hx with hs | ht
  · exact Or.inl ⟨x, hs, rfl⟩
  · exact Or.inr ⟨x, ht, rfl⟩

/-- Relative restriction is preimage under the induced inclusion of domain subtypes. -/
theorem germSupport_restriction {F : RawPresheaf.{u,v} B} {U V : Opens X}
    (h : U ≤ V) (s : GermSections F V) :
    germSupport (germRestriction F h s) =
      (fun x : U => (⟨x.val, h x.property⟩ : V)) ⁻¹' germSupport s := rfl

/-- Ambient restriction cuts the original support down by the smaller actual open. -/
theorem germSupportAmbient_restriction {F : RawPresheaf.{u,v} B} {U V : Opens X}
    (h : U ≤ V) (s : GermSections F V) :
    germSupportAmbient (germRestriction F h s) =
      germSupportAmbient s ∩ (U : Set X) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨⟨y.val, h y.property⟩, hy, rfl⟩, y.property⟩
  · rintro ⟨⟨y, hy, rfl⟩, hxU⟩
    exact ⟨⟨y.val, hxU⟩, hy, rfl⟩

/-- Additive stalk maps preserve zero, so no injectivity assumption is needed. -/
theorem germSupport_map_subset {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G)
    (U : Opens X) (s : GermSections F U) :
    germSupport (germSectionsMap φ U s) ⊆ germSupport s := by
  intro x hx
  change rawStalkMap φ x.val (s.val x) ≠ 0 at hx
  change s.val x ≠ 0
  intro hs
  exact hx (by rw [hs, map_zero])

theorem germSupportAmbient_map_subset {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G)
    (U : Opens X) (s : GermSections F U) :
    germSupportAmbient (germSectionsMap φ U s) ⊆ germSupportAmbient s := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, germSupport_map_subset φ U s hx, rfl⟩

@[simp]
theorem germSupport_empty {F : RawPresheaf.{u,v} B}
    (s : GermSections F (⊥ : Opens X)) : germSupport s = ∅ := by
  ext x
  exact False.elim x.property

@[simp]
theorem germSupportAmbient_empty {F : RawPresheaf.{u,v} B}
    (s : GermSections F (⊥ : Opens X)) : germSupportAmbient s = ∅ := by
  simp [germSupportAmbient]

/-- Compactness of relative support is exactly compactness of its ambient image. -/
theorem isCompact_germSupport_iff {F : RawPresheaf.{u,v} B} {U : Opens X}
    (s : GermSections F U) :
    IsCompact (germSupport s) ↔ IsCompact (germSupportAmbient s) :=
  Subtype.isCompact_iff

/-- The actual set denoted by compactly supported sections in the germ model. -/
def compactGermSectionsSet (F : RawPresheaf.{u,v} B) (U : Opens X) :
    Set (GermSections F U) :=
  {s | IsCompact (germSupport s)}

@[simp]
theorem mem_compactGermSectionsSet (F : RawPresheaf.{u,v} B) (U : Opens X)
    (s : GermSections F U) :
    s ∈ compactGermSectionsSet F U ↔ IsCompact (germSupport s) := Iff.rfl

theorem mem_compactGermSectionsSet_iff_ambient (F : RawPresheaf.{u,v} B)
    (U : Opens X) (s : GermSections F U) :
    s ∈ compactGermSectionsSet F U ↔ IsCompact (germSupportAmbient s) :=
  isCompact_germSupport_iff s

@[simp]
theorem zero_mem_compactGermSectionsSet (F : RawPresheaf.{u,v} B) (U : Opens X) :
    (0 : GermSections F U) ∈ compactGermSectionsSet F U := by
  simp

/-- Only a subtype carrier is asserted here; its additive structure is separate. -/
abbrev CompactGermSections (F : RawPresheaf.{u,v} B) (U : Opens X) :
    Type (max u v) :=
  ↥(compactGermSectionsSet F U)

/-- Forget compactness of support, retaining the same actual germ section. -/
def compactGermSectionsInclusion (F : RawPresheaf.{u,v} B) (U : Opens X) :
    CompactGermSections F U → GermSections F U :=
  Subtype.val

@[simp]
theorem compactGermSectionsInclusion_apply (F : RawPresheaf.{u,v} B) (U : Opens X)
    (s : CompactGermSections F U) :
    compactGermSectionsInclusion F U s = s.val := rfl

theorem compactGermSectionsInclusion_injective (F : RawPresheaf.{u,v} B)
    (U : Opens X) : Function.Injective (compactGermSectionsInclusion F U) :=
  Subtype.val_injective

theorem CompactGermSections.isCompact_support {F : RawPresheaf.{u,v} B}
    {U : Opens X} (s : CompactGermSections F U) :
    IsCompact (germSupport s.val) :=
  s.property

end Langlands.Sheaf.Renard
