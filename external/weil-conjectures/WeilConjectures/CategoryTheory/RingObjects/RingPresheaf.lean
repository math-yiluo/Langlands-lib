/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mon

/-!

# Presheaves and sheaves of rings as ring objects in abelian presheaves and abelian sheaves

A *ring object* of a monoidal category is an object `R` with a multiplication `R ⊗ R ⟶ R` and
a unit `𝟙 ⟶ R` which are associative and unital, i.e. an instance `[MonObj R]` in the sense of
mathlib. This file produces ring objects in the category of abelian presheaves `Cᵒᵖ ⥤ Ab`, with
its objectwise tensor product, and in the category of abelian sheaves `Sheaf J Ab` on a site
`(C, J)`, with the monoidal structure `CategoryTheory.Sheaf.monoidalCategory` (sheafification
of the objectwise tensor product), from presheaves of rings `P : Cᵒᵖ ⥤ RingCat`. The monoidal
structure on `Ab` itself is the tensor product of abelian groups, recorded in
`WeilConjectures.CategoryTheory.RingObjects.Ab`.

* A presheaf of rings `P` is a ring object of abelian presheaves, through the identification of
  rings with monoid objects of `Ab` (`AddCommGrpCat.ringMonObj`) and mathlib's equivalence
  `Mon (C ⥤ D) ≌ C ⥤ Mon D`: the underlying abelian presheaf is `P ⋙ forget₂ RingCat Ab`, and
  the multiplication and unit are objectwise those of the rings `P.obj U`. A natural
  transformation of presheaves of rings is a morphism of ring objects. The ring object is
  commutative when the rings `P.obj U` are.
* The sheafification functor `presheafToSheaf J Ab` is monoidal, so it sends ring objects to
  ring objects: the sheafification of a presheaf of rings is a ring object of abelian sheaves,
  `Sheaf.sheafifyRingPresheaf J P`.
* A sheaf of rings `S : Sheaf J RingCat` has an underlying abelian sheaf
  `(sheafCompose J (forget₂ RingCat Ab)).obj S`, which is a ring object: the structure is
  transported along the counit of the sheafification adjunction from the sheafification of the
  presheaf of rings `S.obj`. A morphism of sheaves of rings induces a morphism of ring objects.

## Main definitions

* `CategoryTheory.Functor.toMonAb`: a functor `C ⥤ RingCat` as a monoid object of `C ⥤ Ab`;
  the instance `MonObj (P ⋙ forget₂ RingCat Ab)`.
* `CategoryTheory.Functor.isCommMonObj_compForget₂`: it is commutative when the rings are.
* `CategoryTheory.Sheaf.sheafifyRingPresheaf`: the sheafification of a presheaf of rings, a
  ring object of `Sheaf J Ab`.
* `CategoryTheory.Sheaf.monObj_sheafCompose_obj`: the abelian sheaf underlying a sheaf of
  rings is a ring object, and `CategoryTheory.Sheaf.isMonHom_sheafCompose_map`: a morphism of
  sheaves of rings is a morphism of ring objects.
* `CategoryTheory.Sheaf.sheafComposeToSheafify`: the morphism of ring objects from a sheaf of
  rings to the sheafification of a presheaf of rings induced by a morphism of presheaves of
  rings.

-/

@[expose] public section

universe w v u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace RingCat

/-- The functor sending a ring to the corresponding monoid object of `Ab`. -/
@[simps]
noncomputable def toMonAb : RingCat.{w} ⥤ Mon Ab.{w} where
  obj R := Mon.mk (AddCommGrpCat.of R)
  map f := Mon.Hom.mk (AddCommGrpCat.ofHom f.hom.toAddMonoidHom)

lemma toMonAb_comp_forget : toMonAb.{w} ⋙ Mon.forget Ab.{w} = forget₂ RingCat.{w} Ab.{w} :=
  rfl

end RingCat

namespace Functor

section Presheaf

variable (P : C ⥤ RingCat.{w})

/-- A functor `P : C ⥤ RingCat`, for instance a presheaf of rings, as a monoid object of the
functor category `C ⥤ Ab` with its objectwise monoidal structure: its underlying functor is
`P ⋙ forget₂ RingCat Ab`, and its multiplication and unit are objectwise those of the rings
`P.obj X`. -/
noncomputable def toMonAb : Mon (C ⥤ Ab.{w}) :=
  (Monoidal.monFunctorCategoryEquivalence C Ab.{w}).inverse.obj (P ⋙ RingCat.toMonAb)

lemma toMonAb_X : P.toMonAb.X = P ⋙ forget₂ RingCat.{w} Ab.{w} :=
  rfl

/-- A functor `P : C ⥤ RingCat` makes `P ⋙ forget₂ RingCat Ab` a monoid object of `C ⥤ Ab`. -/
noncomputable instance monObjCompForget₂ : MonObj (P ⋙ forget₂ RingCat.{w} Ab.{w}) :=
  P.toMonAb.mon

lemma one_compForget₂_app (X : C) :
    η[P ⋙ forget₂ RingCat.{w} Ab.{w}].app X = η[AddCommGrpCat.of (P.obj X)] :=
  rfl

lemma mul_compForget₂_app (X : C) :
    μ[P ⋙ forget₂ RingCat.{w} Ab.{w}].app X = μ[AddCommGrpCat.of (P.obj X)] :=
  rfl

/-- The monoid object `P ⋙ forget₂ RingCat Ab` is commutative when all the rings `P.obj X`
are commutative. -/
lemma isCommMonObj_compForget₂ (h : ∀ (X : C) (a b : P.obj X), a * b = b * a) :
    IsCommMonObj (P ⋙ forget₂ RingCat.{w} Ab.{w}) where
  mul_comm := by
    ext X : 2
    exact (AddCommGrpCat.isCommMonObj_of_mul_comm (P.obj X) (h X)).mul_comm

variable {P} {Q : C ⥤ RingCat.{w}} (f : P ⟶ Q)

/-- A natural transformation of functors to `RingCat` is a morphism of monoid objects of
`C ⥤ Ab`. -/
instance isMonHom_whiskerRight_forget₂ :
    IsMonHom (Functor.whiskerRight f (forget₂ RingCat.{w} Ab.{w})) :=
  ((Monoidal.monFunctorCategoryEquivalence C Ab.{w}).inverse.map
    (Functor.whiskerRight f RingCat.toMonAb)).isMonHom_hom

end Presheaf

end Functor

namespace Sheaf

variable (J : GrothendieckTopology C) [HasWeakSheafify J Ab.{w}] [(J.W (A := Ab.{w})).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The sheafification of a monoid object of abelian presheaves is a monoid object of abelian
sheaves, since the sheafification functor is monoidal. -/
noncomputable instance monObj_presheafToSheaf_obj (M : Cᵒᵖ ⥤ Ab.{w}) [MonObj M] :
    MonObj ((presheafToSheaf J Ab.{w}).obj M) :=
  Functor.monObjObj (F := presheafToSheaf J Ab.{w}) M

/-- The sheafification of a commutative monoid object of abelian presheaves is a commutative
monoid object, since the sheafification functor is braided. -/
instance isCommMonObj_presheafToSheaf_obj (M : Cᵒᵖ ⥤ Ab.{w}) [MonObj M] [IsCommMonObj M] :
    IsCommMonObj ((presheafToSheaf J Ab.{w}).obj M) :=
  Functor.isCommMonObj_obj (F := presheafToSheaf J Ab.{w})

/-- The sheafification of a presheaf of rings `P`, as a ring object of the category of abelian
sheaves. Its ring object structure is the instance `Sheaf.monObj_presheafToSheaf_obj`. -/
noncomputable abbrev sheafifyRingPresheaf (P : Cᵒᵖ ⥤ RingCat.{w}) : Sheaf J Ab.{w} :=
  (presheafToSheaf J Ab.{w}).obj (P ⋙ forget₂ RingCat.{w} Ab.{w})

section SheafCompose

variable [J.HasSheafCompose (forget₂ RingCat.{w} Ab.{w})] (S : Sheaf J RingCat.{w})

/-- The counit of the sheafification adjunction, an isomorphism from the sheafification of the
presheaf of rings underlying a sheaf of rings `S` to the abelian sheaf underlying `S`. -/
noncomputable def sheafifyRingPresheafIso :
    sheafifyRingPresheaf J S.obj ≅ (sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S :=
  asIso ((sheafificationAdjunction J Ab.{w}).counit.app
    ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S))

/-- The abelian sheaf underlying a sheaf of rings is a ring object of the category of abelian
sheaves: the structure is transported along the counit of the sheafification adjunction from
the sheafification of the underlying presheaf of rings. -/
noncomputable instance monObj_sheafCompose_obj :
    MonObj ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S) :=
  MonObj.ofIso (sheafifyRingPresheafIso J S)

instance isMonHom_sheafifyRingPresheafIso_hom : IsMonHom (sheafifyRingPresheafIso J S).hom :=
  isMonHom_ofIso _

instance isMonHom_sheafifyRingPresheafIso_inv : IsMonHom (sheafifyRingPresheafIso J S).inv :=
  inferInstance

/-- The abelian sheaf underlying a sheaf of commutative rings is a commutative ring object. -/
lemma isCommMonObj_sheafCompose_obj (h : ∀ (U : Cᵒᵖ) (a b : S.obj.obj U), a * b = b * a) :
    IsCommMonObj ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S) :=
  haveI := S.obj.isCommMonObj_compForget₂ h
  IsCommMonObj.ofIso (sheafifyRingPresheafIso J S)

variable {S} {T : Sheaf J RingCat.{w}} (f : S ⟶ T)

omit [(J.W (A := Ab.{w})).IsMonoidal] in
/-- The morphism of abelian sheaves underlying a morphism of sheaves of rings is conjugate to
the sheafification of the underlying morphism of abelian presheaves by the counit
isomorphisms. -/
lemma sheafCompose_map_eq :
    (sheafCompose J (forget₂ RingCat.{w} Ab.{w})).map f =
      (sheafifyRingPresheafIso J S).inv ≫
        (presheafToSheaf J Ab.{w}).map
          (Functor.whiskerRight f.hom (forget₂ RingCat.{w} Ab.{w})) ≫
        (sheafifyRingPresheafIso J T).hom := by
  rw [Iso.eq_inv_comp]
  exact ((sheafificationAdjunction J Ab.{w}).counit.naturality
    ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).map f)).symm

/-- A morphism of sheaves of rings is a morphism of ring objects. -/
instance isMonHom_sheafCompose_map :
    IsMonHom ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).map f) := by
  rw [sheafCompose_map_eq]
  infer_instance

variable (S) {Q : Cᵒᵖ ⥤ RingCat.{w}} (g : S.obj ⟶ Q)

/-- The morphism of ring objects from the abelian sheaf underlying a sheaf of rings `S` to the
sheafification of a presheaf of rings `Q`, induced by a morphism of presheaves of rings
`S.obj ⟶ Q`. -/
noncomputable def sheafComposeToSheafify :
    (sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S ⟶ sheafifyRingPresheaf J Q :=
  (sheafifyRingPresheafIso J S).inv ≫
    (presheafToSheaf J Ab.{w}).map (Functor.whiskerRight g (forget₂ RingCat.{w} Ab.{w}))

instance isMonHom_sheafComposeToSheafify : IsMonHom (sheafComposeToSheafify J S g) :=
  inferInstanceAs (IsMonHom ((sheafifyRingPresheafIso J S).inv ≫
    (presheafToSheaf J Ab.{w}).map (Functor.whiskerRight g (forget₂ RingCat.{w} Ab.{w}))))

omit [(J.W (A := Ab.{w})).IsMonoidal] in
variable {S} in
/-- Precomposing `sheafComposeToSheafify J S g` with the morphism of abelian sheaves underlying a
morphism of sheaves of rings `f' : S' ⟶ S` gives `sheafComposeToSheafify J S' (f'.hom ≫ g)`. -/
lemma sheafCompose_map_comp_sheafComposeToSheafify {S' : Sheaf J RingCat.{w}} (f' : S' ⟶ S) :
    (sheafCompose J (forget₂ RingCat.{w} Ab.{w})).map f' ≫ sheafComposeToSheafify J S g =
      sheafComposeToSheafify J S' (f'.hom ≫ g) := by
  rw [sheafCompose_map_eq, sheafComposeToSheafify, sheafComposeToSheafify]
  simp [Functor.whiskerRight_comp]

end SheafCompose

end Sheaf

end CategoryTheory
