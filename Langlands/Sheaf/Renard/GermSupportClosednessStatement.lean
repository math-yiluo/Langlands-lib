import Langlands.Sheaf.Renard.GermSupport

/-!
# Renard II.2.2: local vanishing and relative support closedness

These proposition definitions use the original locally represented germ
sections. Closedness is in the domain open with its subtype topology.
-/

open TopologicalSpace

universe u v

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X] {B : OpenBasis X}

/-- A zero germ value has a contained basis neighborhood of zero section values. -/
def RawGermLocalVanishingStatement (F : RawPresheaf.{u,v} B) : Prop :=
  ∀ (U : Opens X) (s : GermSections F U) (x : U),
    s.val x = 0 →
      ∃ (V : BasisOpen B) (_hxV : x.val ∈ V.obj) (hVU : V.obj ≤ U),
        ∀ (y : X) (hy : y ∈ V.obj), s.val ⟨y, hVU hy⟩ = 0

/-- The literal nonzero support is closed in its actual domain subtype. -/
def RawGermRelativeSupportClosednessStatement (F : RawPresheaf.{u,v} B) : Prop :=
  ∀ (U : Opens X) (s : GermSections F U), IsClosed (germSupport s)

/-- Normalization is forgotten through the same underlying raw presheaf. -/
abbrev NormalizedGermLocalVanishingStatement (F : Presheaf.{u,v} B) : Prop :=
  RawGermLocalVanishingStatement F.obj

/-- Relative support closedness for sections of exactly the normalized raw object. -/
abbrev NormalizedGermRelativeSupportClosednessStatement
    (F : Presheaf.{u,v} B) : Prop :=
  RawGermRelativeSupportClosednessStatement F.obj

/-- The closed four-part target, retaining independent space and section universes. -/
def GermSupportClosednessStatement : Prop :=
  ∀ (X : Type u) (_ : TopologicalSpace X) (B : OpenBasis X),
    (∀ F : RawPresheaf.{u,v} B, RawGermLocalVanishingStatement F) ∧
    (∀ F : RawPresheaf.{u,v} B, RawGermRelativeSupportClosednessStatement F) ∧
    (∀ F : Presheaf.{u,v} B, NormalizedGermLocalVanishingStatement F) ∧
    (∀ F : Presheaf.{u,v} B, NormalizedGermRelativeSupportClosednessStatement F)

end Langlands.Sheaf.Renard
