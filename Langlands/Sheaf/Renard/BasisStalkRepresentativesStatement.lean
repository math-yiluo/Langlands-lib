import Langlands.Sheaf.Renard.BasisStalk

/-!
# Representatives and equality of germs for Renard's basis stalks

These proposition definitions state the representative description of the
published stalk colimits. The space and section-group universes are independent.
-/

universe u v

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X] {B : OpenBasis X}

/-- Every raw stalk element comes from an original section on a basis neighborhood. -/
def RawStalkRepresentativeStatement (F : RawPresheaf.{u,v} B) (x : X) : Prop :=
  ∀ a : rawStalk F x,
    ∃ (U : BasisOpen B) (hx : x ∈ U.obj) (s : Sections F U),
      rawGerm F U x hx s = a

/-- Raw germs agree exactly when original restrictions agree on a smaller basis neighborhood. -/
def RawGermEqualityStatement (F : RawPresheaf.{u,v} B) (x : X) : Prop :=
  ∀ (U V : BasisOpen B) (hxU : x ∈ U.obj) (hxV : x ∈ V.obj)
    (s : Sections F U) (t : Sections F V),
    rawGerm F U x hxU s = rawGerm F V x hxV t ↔
      ∃ W : BasisOpen B, x ∈ W.obj ∧
        ∃ (hWU : W.obj ≤ U.obj) (hWV : W.obj ≤ V.obj),
          restriction F hWU s = restriction F hWV t

/-- Every normalized stalk element comes from an original section on a basis neighborhood. -/
def StalkRepresentativeStatement (F : Presheaf.{u,v} B) (x : X) : Prop :=
  ∀ a : stalk F x,
    ∃ (U : BasisOpen B) (hx : x ∈ U.obj) (s : Sections F.obj U),
      germ F U x hx s = a

/-- Normalized germs agree exactly when original restrictions agree on a smaller basis neighborhood. -/
def GermEqualityStatement (F : Presheaf.{u,v} B) (x : X) : Prop :=
  ∀ (U V : BasisOpen B) (hxU : x ∈ U.obj) (hxV : x ∈ V.obj)
    (s : Sections F.obj U) (t : Sections F.obj V),
    germ F U x hxU s = germ F V x hxV t ↔
      ∃ W : BasisOpen B, x ∈ W.obj ∧
        ∃ (hWU : W.obj ≤ U.obj) (hWV : W.obj ≤ V.obj),
          restriction F.obj hWU s = restriction F.obj hWV t

/-- The complete representative and germ-equality family for arbitrary spaces and chosen bases. -/
def BasisStalkRepresentativesStatement : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (B : OpenBasis X),
    (∀ (F : RawPresheaf.{u,v} B) (x : X),
      RawStalkRepresentativeStatement F x ∧ RawGermEqualityStatement F x) ∧
    (∀ (F : Presheaf.{u,v} B) (x : X),
      StalkRepresentativeStatement F x ∧ GermEqualityStatement F x)

end Langlands.Sheaf.Renard
