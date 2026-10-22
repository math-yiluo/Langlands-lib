import Langlands.AbelianScheme.Basic
import Langlands.AbelianScheme.IsogenyStability

/-! # Isogenies of bundled abelian schemes -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

universe u

variable {S T : Scheme.{u}} {A B C : AbelianScheme S}

/-- The finite-flat-surjective predicate on actual abelian-scheme homomorphisms. -/
abbrev IsIsogeny (f : A ⟶ B) : Prop :=
  GroupScheme.IsIsogeny (groupHom f)

theorem isIsogeny_iff (f : A ⟶ B) :
    IsIsogeny f ↔ IsFinite (hom f) ∧ Flat (hom f) ∧ Surjective (hom f) :=
  Iff.rfl

theorem isIsogeny_id (A : AbelianScheme S) : IsIsogeny (𝟙 A) :=
  GroupScheme.isIsogeny_id A.toGrp

theorem IsIsogeny.comp {f : A ⟶ B} {g : B ⟶ C}
    (hf : IsIsogeny f) (hg : IsIsogeny g) : IsIsogeny (f ≫ g) :=
  GroupScheme.IsIsogeny.comp hf hg

theorem IsIsogeny.baseChange {f : A ⟶ B} (hf : IsIsogeny f) (b : T ⟶ S) :
    IsIsogeny ((baseChange b).map f) :=
  GroupScheme.IsIsogeny.baseChange b hf

end Langlands.AbelianScheme
