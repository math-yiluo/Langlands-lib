import Langlands.Sheaf.Renard.BasisSheaf
import Langlands.Sheaf.Renard.BasisStalk

/-!
# Renard II.2.1: sheaf germ separation and corrected target compatibility

These are proposition definitions, not proofs. Compatibility is tested on
every smaller basis open, and the source presheaf need not be a sheaf.
-/

open CategoryTheory Opposite

universe u v w

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X] {B : OpenBasis X}

/-- The zero-germ separation assertion for a raw presheaf satisfying the literal sheaf axiom. -/
def RawSheafZeroGermSeparationStatement (F : RawPresheaf.{u,v} B) : Prop :=
  SheafCondition F →
    ∀ (U : BasisOpen B) (s : Sections F U),
      (∀ (x : X) (hx : x ∈ U.obj), rawGerm F U x hx s = 0) → s = 0

/-- The whole family of germs detects equality of sections of a raw sheaf. -/
def RawSheafGermEqualityStatement (F : RawPresheaf.{u,v} B) : Prop :=
  SheafCondition F →
    ∀ (U : BasisOpen B) (s t : Sections F U),
      (∀ (x : X) (hx : x ∈ U.obj),
        rawGerm F U x hx s = rawGerm F U x hx t) → s = t

/-- Renard's zero-germ lemma on an actual object of his normalized sheaf category. -/
def SheafZeroGermSeparationStatement (G : BasisSheaf.{u,v} B) : Prop :=
  ∀ (U : BasisOpen B) (s : Sections G.obj.obj U),
    (∀ (x : X) (hx : x ∈ U.obj), germ G.obj U x hx s = 0) → s = 0

/-- Equality detection by all normalized germs on an actual basis sheaf. -/
def SheafGermEqualityStatement (G : BasisSheaf.{u,v} B) : Prop :=
  ∀ (U : BasisOpen B) (s t : Sections G.obj.obj U),
    (∀ (x : X) (hx : x ∈ U.obj),
      germ G.obj U x hx s = germ G.obj U x hx t) → s = t

/-- Equal original germs imply literal compatibility of the images in a target sheaf. -/
def RawTargetGermCompatibilityStatement (F G : RawPresheaf.{u,v} B)
    (ψ : F ⟶ G) : Prop :=
  SheafCondition G →
    ∀ (ι : Type w) (U : ι → BasisOpen B) (s : ∀ i, Sections F (U i)),
      (∀ (i j : ι) (x : X) (hxi : x ∈ (U i).obj) (hxj : x ∈ (U j).obj),
        rawGerm F (U i) x hxi (s i) = rawGerm F (U j) x hxj (s j)) →
      Compatible G U (fun i => ψ.app (op (U i)) (s i))

/-- The corrected target compatibility in the normalized source categories. -/
def TargetGermCompatibilityStatement (F : Presheaf.{u,v} B) (G : BasisSheaf.{u,v} B)
    (ψ : F ⟶ G.obj) : Prop :=
  ∀ (ι : Type w) (U : ι → BasisOpen B) (s : ∀ i, Sections F.obj (U i)),
    (∀ (i j : ι) (x : X) (hxi : x ∈ (U i).obj) (hxj : x ∈ (U j).obj),
      germ F (U i) x hxi (s i) = germ F (U j) x hxj (s j)) →
    Compatible G.obj.obj U (fun i => ψ.hom.app (op (U i)) (s i))

/-- The closed separation and corrected compatibility target, with three independent universes. -/
def RenardSheafGermSeparationStatement : Prop :=
  ∀ (X : Type u) (_ : TopologicalSpace X) (B : OpenBasis X),
    (∀ F : RawPresheaf.{u,v} B, RawSheafZeroGermSeparationStatement F) ∧
    (∀ F : RawPresheaf.{u,v} B, RawSheafGermEqualityStatement F) ∧
    (∀ G : BasisSheaf.{u,v} B, SheafZeroGermSeparationStatement G) ∧
    (∀ G : BasisSheaf.{u,v} B, SheafGermEqualityStatement G) ∧
    (∀ (F G : RawPresheaf.{u,v} B) (ψ : F ⟶ G),
      RawTargetGermCompatibilityStatement.{u,v,w} F G ψ) ∧
    (∀ (F : Presheaf.{u,v} B) (G : BasisSheaf.{u,v} B) (ψ : F ⟶ G.obj),
      TargetGermCompatibilityStatement.{u,v,w} F G ψ)

end Langlands.Sheaf.Renard
