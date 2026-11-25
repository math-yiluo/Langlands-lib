/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Opposites

/-!
# Contravariant self-equivalences of full subcategories

Let `D : Cᵒᵖ ⥤ C` be a contravariant endofunctor of a category `C`, with a natural
transformation `δ : 𝟭 C ⟶ D.rightOp ⋙ D`, the *double-dual map* `δ_K : K ⟶ D (D K)`. If a
property `P` of objects of `C` is preserved by `D` and `δ_K` is an isomorphism for every `K`
satisfying `P`, then `D` restricts to an equivalence `P.FullSubcategoryᵒᵖ ≌ P.FullSubcategory`,
its own quasi-inverse. This is the shape of Verdier biduality.

## Main definitions

- `CategoryTheory.ObjectProperty.liftDual`: the restriction `P.FullSubcategoryᵒᵖ ⥤
  P.FullSubcategory` of `D`.
- `CategoryTheory.ObjectProperty.liftDualEquivalence`: the anti-equivalence of
  `P.FullSubcategory` it induces when `δ` is an isomorphism on `P`.
-/

@[expose] public section

open Opposite

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category* C] (P : ObjectProperty C) (D : Cᵒᵖ ⥤ C)
  (hD : ∀ K, P K → P (D.obj (op K)))

/-- The restriction `P.FullSubcategoryᵒᵖ ⥤ P.FullSubcategory` of a contravariant endofunctor
`D : Cᵒᵖ ⥤ C` preserving `P`. -/
def liftDual : P.FullSubcategoryᵒᵖ ⥤ P.FullSubcategory :=
  P.lift (P.ι.op ⋙ D) fun K ↦ hD _ K.unop.property

variable (δ : 𝟭 C ⟶ D.rightOp ⋙ D) (hδ : ∀ K, P K → IsIso (δ.app K))

/-- The double-dual isomorphism `K ≅ D (D K)` in `P.FullSubcategory`. -/
noncomputable def liftDualIso (K : P.FullSubcategory) :
    K ≅ (P.liftDual D hD).obj (op ((P.liftDual D hD).obj (op K))) :=
  have := hδ K.obj K.property
  P.isoMk (asIso (δ.app K.obj))

lemma liftDualIso_hom_naturality {K L : P.FullSubcategory} (f : K ⟶ L) :
    f ≫ (P.liftDualIso D hD δ hδ L).hom =
      (P.liftDualIso D hD δ hδ K).hom ≫ (P.liftDual D hD).map ((P.liftDual D hD).map f.op).op :=
  P.hom_ext (δ.naturality f.hom)

/-- If `D` preserves `P` and the double-dual map `δ_K : K ⟶ D (D K)` is an isomorphism for every
`K` satisfying `P`, then `D` restricts to an anti-equivalence of `P.FullSubcategory`, with
quasi-inverse `D` itself. -/
noncomputable def liftDualEquivalence : P.FullSubcategoryᵒᵖ ≌ P.FullSubcategory :=
  Equivalence.mk (P.liftDual D hD) (P.liftDual D hD).rightOp
    (NatIso.ofComponents (fun K ↦ (P.liftDualIso D hD δ hδ K.unop).op.symm) fun f ↦
      Quiver.Hom.unop_inj (by
        dsimp
        simp only [Iso.op_inv, Quiver.Hom.unop_op]
        rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, liftDualIso_hom_naturality,
          Quiver.Hom.op_unop]))
    (NatIso.ofComponents (fun K ↦ (P.liftDualIso D hD δ hδ K).symm) fun f ↦ by
      dsimp
      rw [Iso.comp_inv_eq, Category.assoc, liftDualIso_hom_naturality, Iso.inv_hom_id_assoc])

end CategoryTheory.ObjectProperty
