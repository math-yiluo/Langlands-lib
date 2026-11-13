/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.GaloisSubextension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.Definitions

/-!
# NYLL M040: finite Galois subextension data

Modified by Worker 4918: extract the source data, instance and construction
units listed in the paired Markdown from the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`,
prefix the namespace with `Langlands.NYLL`, and replace the source module import
by the focused published imports these declarations use. Inside the proof fields
of `compositum` the unpublished source lemma `mem_extensionSubgroup_iff` is
replaced by Mathlib's `Subgroup.mem_subgroupOf`. The paired Markdown records
every modification. See `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A finite Galois extension `L / K`, represented by `G_L ≤ G_K`. -/
structure FiniteGaloisSubextension (K : ClosedSubgroup G) where
  /-- The closed subgroup representing the top field. -/
  field : ClosedSubgroup G
  /-- The top-field subgroup is contained in the base-field subgroup. -/
  below : field.toSubgroup ≤ K.toSubgroup
  /-- The top-field subgroup is normal inside the base-field subgroup. -/
  normal : (extensionSubgroup K field below).Normal
  /-- The relative Galois quotient is finite. -/
  finite : Finite (K.toSubgroup ⧸ extensionSubgroup K field below)

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- Forget only finiteness from a finite Galois subextension. -/
def toGaloisSubextension (L : FiniteGaloisSubextension K) :
    DegreeData.GaloisSubextension K where
  field := L.field
  below := L.below
  normal := L.normal

/-- Forget normality, retaining the underlying finite abstract extension.
This is the canonical bridge from a finite Galois subextension to the degree
and ramification API. -/
def toFiniteAbstractExtension (L : FiniteGaloisSubextension K) :
    DegreeData.FiniteAbstractExtension G where
  field := L.field
  base := K
  below := L.below
  finiteQuotient := L.finite

/-- The actual finite quotient `G(L/K)`, kept behind a named object
boundary. -/
def extensionQuotient (L : FiniteGaloisSubextension K) : Type u :=
  K.toSubgroup ⧸ extensionSubgroup K L.field L.below

/-- Structural unramifiedness of the underlying finite extension. -/
def IsUnramified (L : FiniteGaloisSubextension K) (D : DegreeData G) : Prop :=
  L.toFiniteAbstractExtension.IsUnramified D

/-- Structural total ramification of the underlying finite extension. -/
def IsTotallyRamified (L : FiniteGaloisSubextension K)
    (D : DegreeData G) : Prop :=
  L.toFiniteAbstractExtension.IsTotallyRamified D

/-- A finite Galois subextension is represented by a normal subgroup. -/
instance extensionSubgroup_normalInstance (L : FiniteGaloisSubextension K) :
    (extensionSubgroup K L.field L.below).Normal :=
  L.normal

/-- The group structure transported across the named finite quotient
boundary. -/
instance extensionQuotient_groupInstance (L : FiniteGaloisSubextension K) :
    Group L.extensionQuotient := by
  change Group
    (K.toSubgroup ⧸ extensionSubgroup K L.field L.below)
  infer_instance

/-- The quotient represented by a finite Galois subextension is finite. -/
instance extensionQuotient_finiteInstance (L : FiniteGaloisSubextension K) :
    Finite L.extensionQuotient :=
  L.finite

/-- Comparison with the quotient presentation used by the underlying group
library. -/
def extensionQuotientMulEquiv (L : FiniteGaloisSubextension K) :
    L.extensionQuotient ≃*
      (K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
  MulEquiv.refl _

/-- The canonical quotient projection for a finite Galois subextension. -/
def extensionQuotientMk (L : FiniteGaloisSubextension K) :
    K.toSubgroup →* L.extensionQuotient :=
  QuotientGroup.mk' (extensionSubgroup K L.field L.below)

/-- The finite and non-finite Galois bundles have the same quotient; this
named equivalence is the only public comparison needed by clients. -/
def toGaloisExtensionQuotientMulEquiv (L : FiniteGaloisSubextension K) :
    L.extensionQuotient ≃* L.toGaloisSubextension.extensionQuotient :=
  L.extensionQuotientMulEquiv.trans
    L.toGaloisSubextension.extensionQuotientMulEquiv.symm

/-- The trivial extension `K / K`. -/
def refl (K : ClosedSubgroup G) : FiniteGaloisSubextension K where
  field := K
  below := le_rfl
  normal := by
    have htop : extensionSubgroup K K le_rfl = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact x.2
    rw [htop]
    infer_instance
  finite := by
    have htop : extensionSubgroup K K le_rfl = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact x.2
    rw [htop]
    infer_instance

/-- The compositum `L₁L₂`, represented by `G_{L₁} ∩ G_{L₂}`. -/
def compositum (L₁ L₂ : FiniteGaloisSubextension K) :
    FiniteGaloisSubextension K where
  field := L₁.field ⊓ L₂.field
  below := fun _ h => L₁.below h.1
  normal := by
    have heq : extensionSubgroup K (L₁.field ⊓ L₂.field)
        (fun _ h => L₁.below h.1) =
        extensionSubgroup K L₁.field L₁.below ⊓
          extensionSubgroup K L₂.field L₂.below := by
      ext k
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      constructor
      · intro hk
        exact ⟨hk.1, hk.2⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, h₂⟩
    rw [heq]
    let : (extensionSubgroup K L₁.field L₁.below).Normal := L₁.normal
    let : (extensionSubgroup K L₂.field L₂.below).Normal := L₂.normal
    infer_instance
  finite := by
    have heq : extensionSubgroup K (L₁.field ⊓ L₂.field)
        (fun _ h => L₁.below h.1) =
        extensionSubgroup K L₁.field L₁.below ⊓
          extensionSubgroup K L₂.field L₂.below := by
      ext k
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      constructor
      · intro hk
        exact ⟨hk.1, hk.2⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, h₂⟩
    let : (extensionSubgroup K L₁.field L₁.below).FiniteIndex :=
      @Subgroup.finiteIndex_of_finite_quotient K.toSubgroup _
        (extensionSubgroup K L₁.field L₁.below) L₁.finite
    let : (extensionSubgroup K L₂.field L₂.below).FiniteIndex :=
      @Subgroup.finiteIndex_of_finite_quotient K.toSubgroup _
        (extensionSubgroup K L₂.field L₂.below) L₂.finite
    rw [heq]
    exact Subgroup.finite_quotient_of_finiteIndex

end FiniteGaloisSubextension

end GroupOnly

end
end Langlands.NYLL.ClassFormation
