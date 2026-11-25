/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-!
# The unit of the lax monoidal functor from sheaves to presheaves

For the localized monoidal structure `Sheaf.monoidalCategory` on `Sheaf J A`, the unit of
`Sheaf J A` is the sheafification of the unit presheaf, and the unit
`ε : 𝟙_ ⟶ (𝟙_ : Sheaf J A).obj` of the lax monoidal functor `sheafToPresheaf J A` is the unit
`toSheafify J 𝟙_` of the sheafification adjunction
(`CategoryTheory.ε_sheafToPresheaf_eq_toSheafify`).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {A : Type*} [Category* A]
  [MonoidalCategory A] [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]

attribute [local instance] Sheaf.monoidalCategory

/-- The unit `ε : 𝟙_ ⟶ (𝟙_ : Sheaf J A).obj` of the lax monoidal functor `sheafToPresheaf J A`
is the unit `toSheafify J 𝟙_` of the sheafification adjunction. -/
lemma ε_sheafToPresheaf_eq_toSheafify :
    ε (sheafToPresheaf J A) = toSheafify J (𝟙_ (Cᵒᵖ ⥤ A)) :=
  (Adjunction.homEquiv_unit _ _ _ _).trans (Category.comp_id _)

end CategoryTheory
