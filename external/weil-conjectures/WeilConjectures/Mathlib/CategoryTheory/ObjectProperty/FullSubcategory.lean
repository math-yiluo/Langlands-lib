/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Functors between full subcategories

A functor `F : C ⥤ D` which sends the objects satisfying `P` to objects satisfying `Q` induces
a functor `P.liftFullSubcategory Q F h : P.FullSubcategory ⥤ Q.FullSubcategory`. It agrees
with `Q.lift (P.ι ⋙ F) _`, but its value at `X` is `⟨F.obj X.obj, _⟩` on the nose: no
composite `(P.ι ⋙ F).obj X` has to be unfolded when typechecking terms built from it, which
the kernel can find expensive when `F` is a large definition.
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

variable {C D : Type*} [Category* C] [Category* D] (P : ObjectProperty C) (Q : ObjectProperty D)

/-- The functor between full subcategories induced by a functor `F : C ⥤ D` sending objects
satisfying `P` to objects satisfying `Q`. -/
@[simps]
def liftFullSubcategory (F : C ⥤ D) (h : ∀ X, P X → Q (F.obj X)) :
    P.FullSubcategory ⥤ Q.FullSubcategory where
  obj X := ⟨F.obj X.obj, h X.obj X.property⟩
  map f := Q.homMk (F.map f.hom)

/-- `P.liftFullSubcategory Q F h` followed by the inclusion of `Q` is the inclusion of `P`
followed by `F`. -/
def liftFullSubcategoryCompιIso (F : C ⥤ D) (h : ∀ X, P X → Q (F.obj X)) :
    P.liftFullSubcategory Q F h ⋙ Q.ι ≅ P.ι ⋙ F :=
  Iso.refl _

/-- A natural transformation `α : F ⟶ G` induces a natural transformation between the induced
functors between full subcategories. -/
@[simps]
def liftFullSubcategoryMap {F G : C ⥤ D} (α : F ⟶ G) (hF : ∀ X, P X → Q (F.obj X))
    (hG : ∀ X, P X → Q (G.obj X)) :
    P.liftFullSubcategory Q F hF ⟶ P.liftFullSubcategory Q G hG where
  app X := Q.homMk (α.app X.obj)
  naturality _ _ f := Q.hom_ext (α.naturality f.hom)

/-- The functor between full subcategories induced by an additive functor is additive. -/
lemma liftFullSubcategory_additive [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (h : ∀ X, P X → Q (F.obj X)) : (P.liftFullSubcategory Q F h).Additive where
  map_add := Q.hom_ext F.map_add

attribute [instance] liftFullSubcategory_additive

/-- The functor between full subcategories induced by a full functor is full. -/
lemma liftFullSubcategory_full (F : C ⥤ D) [F.Full] (h : ∀ X, P X → Q (F.obj X)) :
    (P.liftFullSubcategory Q F h).Full where
  map_surjective g := ⟨P.homMk (F.preimage g.hom), Q.hom_ext (F.map_preimage g.hom)⟩

/-- The functor between full subcategories induced by a faithful functor is faithful. -/
lemma liftFullSubcategory_faithful (F : C ⥤ D) [F.Faithful] (h : ∀ X, P X → Q (F.obj X)) :
    (P.liftFullSubcategory Q F h).Faithful where
  map_injective e := P.hom_ext (F.map_injective (congrArg (·.hom) e))

attribute [instance] liftFullSubcategory_full liftFullSubcategory_faithful

section LiftCompι

variable {E : Type*} [Category* E] (R : ObjectProperty D) (F : E ⥤ D) (hF : ∀ X, R (F.obj X))

/-- The components of `R.liftCompιIso F hF` are identities. -/
@[simp]
lemma liftCompιIso_hom_app (X : E) : (R.liftCompιIso F hF).hom.app X = 𝟙 _ := rfl

/-- The components of the inverse of `R.liftCompιIso F hF` are identities. -/
@[simp]
lemma liftCompιIso_inv_app (X : E) : (R.liftCompιIso F hF).inv.app X = 𝟙 _ := rfl

end LiftCompι

end CategoryTheory.ObjectProperty
