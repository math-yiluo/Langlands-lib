/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Localization.Adjunction
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-!
# The adjunction induced on complexes, on the homotopy category, and on its bounded part

An adjunction `G ⊣ F` of additive functors induces an adjunction
`G.mapHomologicalComplex c ⊣ F.mapHomologicalComplex c` between the induced functors on
categories of homological complexes (`CategoryTheory.Adjunction.mapHomologicalComplex`),
with unit and counit given degreewise by the unit and counit of `adj`.

Since `HomotopyCategory.quotient` is a localization functor for the homotopy equivalences,
that adjunction descends to the homotopy categories
(`CategoryTheory.Adjunction.mapHomotopyCategory`), and restricting along the fully faithful
inclusions of the bounded below subcategories gives an adjunction between the bounded below
homotopy categories (`CategoryTheory.Adjunction.mapHomotopyCategoryPlus`).

We also record how these adjunctions behave under identities and composition: the unit of
the adjunction induced by `Adjunction.id` is the inverse of the isomorphism
`Functor.mapHomotopyCategoryPlusIdIso` followed by the image of that inverse under
`(𝟭 C).mapHomotopyCategoryPlus`, and the unit of the adjunction induced by a
composite `adj₁.comp adj₂` is the composite of the two units, transported along
`Functor.mapHomotopyCategoryPlusCompIso`. Both are proved by descending to categories of
complexes, where the unit is given degreewise by the unit of `adj`.

## Main definitions

- `CategoryTheory.Adjunction.mapHomologicalComplex`
- `CategoryTheory.Adjunction.mapHomotopyCategory`
- `CategoryTheory.Adjunction.mapHomotopyCategoryPlus`

## Main results

- `CategoryTheory.Adjunction.mapHomotopyCategoryPlus_id_unit_app`: the identity law, and
  `CategoryTheory.Adjunction.mapHomotopyCategoryPlus_id_unit_app_eq_id`: the induced unit
  is in fact the identity.
- `CategoryTheory.Adjunction.mapHomotopyCategoryPlus_comp_unit_app`: the composition law.
- `CategoryTheory.Adjunction.mapHomotopyCategoryPlus_unit_app_comp`: if two adjunctions
  `LA ⊣ RA` and `LB ⊣ RB` between the same pair of categories come with natural
  transformations `u : LA ⟶ LB` and `l : RB ⟶ RA` that are conjugate to each other, in the
  form of the unit relation `adjA.unit ≫ RA(u) = adjB.unit ≫ l`, then the same relation
  holds for the induced adjunctions on the bounded below homotopy categories.
- `CategoryTheory.NatTrans.mapHomotopyCategoryPlus_mateEquiv_app`: the mate of a square,
  induced on the bounded below homotopy categories, is the mate of the induced square with
  respect to the induced adjunctions.
- `CategoryTheory.Adjunction.mapHomotopyCategoryPlus_unit_app_comp_id`: the special case
  `adjB = Adjunction.id` of the previous statement, for an adjunction `L ⊣ R` of
  endofunctors and isomorphisms `L ≅ 𝟭`, `R ≅ 𝟭`.
- `CategoryTheory.Adjunction.mapHomotopyCategoryPlus_unit_app_comp_whisker`: the variant of
  `CategoryTheory.Adjunction.mapHomotopyCategoryPlus_unit_app_comp` for adjunctions with different
  targets related by a functor.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] {ι : Type*} (c : ComplexShape ι)

/-- An adjunction `G ⊣ F` of additive functors induces an adjunction
`G.mapHomologicalComplex c ⊣ F.mapHomologicalComplex c` between the induced functors on
categories of homological complexes. (blueprint: `lem-weil-pbc-termwise-adjunction-homotopy`) -/
noncomputable def Adjunction.mapHomologicalComplex {G : D ⥤ C} {F : C ⥤ D} (adj : G ⊣ F)
    [G.Additive] [F.Additive] :
    G.mapHomologicalComplex c ⊣ F.mapHomologicalComplex c where
  unit :=
    { app := fun M =>
        { f := fun n => adj.unit.app (M.X n)
          comm' := fun i j _ => (adj.unit.naturality (M.d i j)).symm }
      naturality := fun M N φ => by
        ext n
        exact adj.unit.naturality (φ.f n) }
  counit :=
    { app := fun K =>
        { f := fun n => adj.counit.app (K.X n)
          comm' := fun i j _ => (adj.counit.naturality (K.d i j)).symm }
      naturality := fun K L ψ => by
        ext n
        exact adj.counit.naturality (ψ.f n) }
  left_triangle_components X := by
    ext n
    exact adj.left_triangle_components (X.X n)
  right_triangle_components Y := by
    ext n
    exact adj.right_triangle_components (Y.X n)

/-- An adjunction `G ⊣ F` of additive functors induces an adjunction
`G.mapHomotopyCategory c ⊣ F.mapHomotopyCategory c` between the induced functors on the
homotopy categories: both induced functors factor the corresponding functors on complexes
through the quotient functors, which are localization functors for the homotopy
equivalences, so `Adjunction.mapHomologicalComplex` descends.
(blueprint: `lem-weil-pbc-termwise-adjunction-homotopy`) -/
noncomputable def Adjunction.mapHomotopyCategory {G : D ⥤ C} {F : C ⥤ D} (adj : G ⊣ F)
    [G.Additive] [F.Additive]
    [(HomotopyCategory.quotient C c).IsLocalization
      (HomologicalComplex.homotopyEquivalences C c)]
    [(HomotopyCategory.quotient D c).IsLocalization
      (HomologicalComplex.homotopyEquivalences D c)] :
    G.mapHomotopyCategory c ⊣ F.mapHomotopyCategory c := by
  letI : CatCommSq (G.mapHomologicalComplex c) (HomotopyCategory.quotient D c)
      (HomotopyCategory.quotient C c) (G.mapHomotopyCategory c) :=
    ⟨(G.mapHomotopyCategoryFactors c).symm⟩
  letI : CatCommSq (F.mapHomologicalComplex c) (HomotopyCategory.quotient C c)
      (HomotopyCategory.quotient D c) (F.mapHomotopyCategory c) :=
    ⟨(F.mapHomotopyCategoryFactors c).symm⟩
  exact (adj.mapHomologicalComplex c).localization
    (HomotopyCategory.quotient D c) (HomologicalComplex.homotopyEquivalences D c)
    (HomotopyCategory.quotient C c) (HomologicalComplex.homotopyEquivalences C c)
    (G.mapHomotopyCategory c) (F.mapHomotopyCategory c)

/-- An adjunction `G ⊣ F` of additive functors induces an adjunction
`G.mapHomotopyCategoryPlus ⊣ F.mapHomotopyCategoryPlus` between the bounded below homotopy
categories: both functors are restrictions of the corresponding functors on the ambient
homotopy categories along the fully faithful inclusions of the bounded below
subcategories. (blueprint: `lem-weil-pbc-termwise-adjunction-homotopy`) -/
noncomputable def Adjunction.mapHomotopyCategoryPlus [Limits.HasBinaryBiproducts C]
    [Limits.HasBinaryBiproducts D] {G : D ⥤ C} {F : C ⥤ D} (adj : G ⊣ F)
    [G.Additive] [F.Additive] :
    G.mapHomotopyCategoryPlus ⊣ F.mapHomotopyCategoryPlus :=
  Adjunction.restrictFullyFaithful (adj.mapHomotopyCategory (ComplexShape.up ℤ))
    (HomotopyCategory.plus D).fullyFaithfulι (HomotopyCategory.plus C).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

namespace Adjunction

section MapHomologicalComplex

variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.Additive] [R.Additive]

@[simp]
lemma mapHomologicalComplex_unit_app_f (X : HomologicalComplex C c) (n : ι) :
    ((adj.mapHomologicalComplex c).unit.app X).f n = adj.unit.app (X.X n) := rfl

@[simp]
lemma mapHomologicalComplex_counit_app_f (Y : HomologicalComplex D c) (n : ι) :
    ((adj.mapHomologicalComplex c).counit.app Y).f n = adj.counit.app (Y.X n) := rfl

end MapHomologicalComplex

/-- The identity law for `Adjunction.mapHomologicalComplex`: the unit of the adjunction
induced by `Adjunction.id` is the inverse of `Functor.mapHomologicalComplexIdIso` followed
by the image of that inverse under `(𝟭 C).mapHomologicalComplex c`. -/
lemma mapHomologicalComplex_id_unit_app (X : HomologicalComplex C c) :
    ((Adjunction.id (C := C)).mapHomologicalComplex c).unit.app X =
      (Functor.mapHomologicalComplexIdIso C c).inv.app X ≫
        ((𝟭 C).mapHomologicalComplex c).map
          ((Functor.mapHomologicalComplexIdIso C c).inv.app X) := by
  ext n
  simp

variable {E : Type u₃} [Category.{v₃} E] [Preadditive E]

/-- The composition law for `Adjunction.mapHomologicalComplex`: the unit of the adjunction
induced by a composite of adjunctions is the composite of the two units, transported along
`Functor.mapHomologicalComplexCompIso`. -/
lemma mapHomologicalComplex_comp_unit_app {L₁ : C ⥤ D} {R₁ : D ⥤ C} (adj₁ : L₁ ⊣ R₁)
    {L₂ : D ⥤ E} {R₂ : E ⥤ D} (adj₂ : L₂ ⊣ R₂)
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    (X : HomologicalComplex C c) :
    ((adj₁.comp adj₂).mapHomologicalComplex c).unit.app X =
      (adj₁.mapHomologicalComplex c).unit.app X ≫
        (R₁.mapHomologicalComplex c).map ((adj₂.mapHomologicalComplex c).unit.app
          ((L₁.mapHomologicalComplex c).obj X)) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (R₂ ⋙ R₁)) c).hom.app
          ((L₂.mapHomologicalComplex c).obj ((L₁.mapHomologicalComplex c).obj X)) ≫
        ((R₂ ⋙ R₁).mapHomologicalComplex c).map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (L₁ ⋙ L₂)) c).hom.app X) := by
  have e₁ : (Functor.mapHomologicalComplexCompIso (Iso.refl (L₁ ⋙ L₂)) c).hom.app X = 𝟙 _ := rfl
  have e₂ : ∀ Z, (Functor.mapHomologicalComplexCompIso (Iso.refl (R₂ ⋙ R₁)) c).hom.app Z =
      𝟙 _ := fun _ => rfl
  rw [e₁, e₂]
  ext n
  simp only [Functor.id_obj, Functor.comp_obj, mapHomologicalComplex_unit_app_f, comp_unit_app,
    Functor.map_id, Category.comp_id, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f]
  rfl

section Localization

variable [(HomotopyCategory.quotient C c).IsLocalization
    (HomologicalComplex.homotopyEquivalences C c)]

/-- The unit of `Adjunction.mapHomotopyCategory` on the image of a complex is the image of
the unit of `Adjunction.mapHomologicalComplex`. -/
lemma mapHomotopyCategory_unit_app_quotient {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.Additive] [R.Additive]
    [(HomotopyCategory.quotient D c).IsLocalization
      (HomologicalComplex.homotopyEquivalences D c)]
    (X : HomologicalComplex C c) :
    (adj.mapHomotopyCategory c).unit.app ((HomotopyCategory.quotient C c).obj X) =
      (HomotopyCategory.quotient C c).map ((adj.mapHomologicalComplex c).unit.app X) := by
  have key : (R.mapHomotopyCategoryFactors c).inv.app ((L.mapHomologicalComplex c).obj X) ≫
      (R.mapHomotopyCategory c).map ((L.mapHomotopyCategoryFactors c).inv.app X) =
      𝟙 ((R.mapHomotopyCategory c).obj
        ((L.mapHomotopyCategory c).obj ((HomotopyCategory.quotient C c).obj X))) := by
    simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv, Functor.comp_obj]
    rw [(R.mapHomotopyCategory c).map_id]
    apply Category.comp_id
  rw [Adjunction.mapHomotopyCategory, Adjunction.localization_unit_app]
  exact (congrArg (fun t => (HomotopyCategory.quotient C c).map
      ((adj.mapHomologicalComplex c).unit.app X) ≫ t) key).trans (Category.comp_id _)

/-- The counit of `Adjunction.mapHomotopyCategory` on the image of a complex is the image of
the counit of `Adjunction.mapHomologicalComplex`. -/
lemma mapHomotopyCategory_counit_app_quotient {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.Additive] [R.Additive]
    [(HomotopyCategory.quotient D c).IsLocalization
      (HomologicalComplex.homotopyEquivalences D c)]
    (X : HomologicalComplex D c) :
    (adj.mapHomotopyCategory c).counit.app ((HomotopyCategory.quotient D c).obj X) =
      (HomotopyCategory.quotient D c).map ((adj.mapHomologicalComplex c).counit.app X) := by
  rw [Adjunction.mapHomotopyCategory, Adjunction.localization_counit_app]
  simp only [Functor.mapHomotopyCategoryFactors, Functor.comp_obj]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]

/-- The identity law for `Adjunction.mapHomotopyCategory`. -/
lemma mapHomotopyCategory_id_unit_app (Y : HomotopyCategory C c) :
    ((Adjunction.id (C := C)).mapHomotopyCategory c).unit.app Y =
      (Functor.mapHomotopyCategoryIdIso C c).inv.app Y ≫
        ((𝟭 C).mapHomotopyCategory c).map ((Functor.mapHomotopyCategoryIdIso C c).inv.app Y) := by
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  have hmap : ∀ {A B : HomologicalComplex C c} (f : A ⟶ B),
      ((𝟭 C).mapHomotopyCategory c).map ((HomotopyCategory.quotient C c).map f) =
        (HomotopyCategory.quotient C c).map (((𝟭 C).mapHomologicalComplex c).map f) :=
    fun _ => rfl
  rw [mapHomotopyCategory_unit_app_quotient, Functor.mapHomotopyCategoryIdIso_inv_app, hmap,
    ← Functor.map_comp, ← mapHomologicalComplex_id_unit_app]

/-- The composition law for `Adjunction.mapHomotopyCategory`. -/
lemma mapHomotopyCategory_comp_unit_app {L₁ : C ⥤ D} {R₁ : D ⥤ C} (adj₁ : L₁ ⊣ R₁)
    {L₂ : D ⥤ E} {R₂ : E ⥤ D} (adj₂ : L₂ ⊣ R₂)
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [(HomotopyCategory.quotient D c).IsLocalization
      (HomologicalComplex.homotopyEquivalences D c)]
    [(HomotopyCategory.quotient E c).IsLocalization
      (HomologicalComplex.homotopyEquivalences E c)]
    (Y : HomotopyCategory C c) :
    ((adj₁.comp adj₂).mapHomotopyCategory c).unit.app Y =
      (adj₁.mapHomotopyCategory c).unit.app Y ≫
        (R₁.mapHomotopyCategory c).map ((adj₂.mapHomotopyCategory c).unit.app
          ((L₁.mapHomotopyCategory c).obj Y)) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (R₂ ⋙ R₁)) c).hom.app
          ((L₂.mapHomotopyCategory c).obj ((L₁.mapHomotopyCategory c).obj Y)) ≫
        ((R₂ ⋙ R₁).mapHomotopyCategory c).map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (L₁ ⋙ L₂)) c).hom.app Y) := by
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  have hmapR₁ : ∀ {A B : HomologicalComplex D c} (f : A ⟶ B),
      (R₁.mapHomotopyCategory c).map ((HomotopyCategory.quotient D c).map f) =
        (HomotopyCategory.quotient C c).map ((R₁.mapHomologicalComplex c).map f) := fun _ => rfl
  have hmapR : ∀ {A B : HomologicalComplex E c} (f : A ⟶ B),
      ((R₂ ⋙ R₁).mapHomotopyCategory c).map ((HomotopyCategory.quotient E c).map f) =
        (HomotopyCategory.quotient C c).map (((R₂ ⋙ R₁).mapHomologicalComplex c).map f) :=
    fun _ => rfl
  have h₂ : (adj₂.mapHomotopyCategory c).unit.app
      ((L₁.mapHomotopyCategory c).obj ((HomotopyCategory.quotient C c).obj X)) =
      (HomotopyCategory.quotient D c).map ((adj₂.mapHomologicalComplex c).unit.app
        ((L₁.mapHomologicalComplex c).obj X)) :=
    mapHomotopyCategory_unit_app_quotient c adj₂ _
  have hciL : (Functor.mapHomotopyCategoryCompIso (Iso.refl (L₁ ⋙ L₂)) c).hom.app
      ((HomotopyCategory.quotient C c).obj X) =
      (HomotopyCategory.quotient E c).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (L₁ ⋙ L₂)) c).hom.app X) := rfl
  have hciR : (Functor.mapHomotopyCategoryCompIso (Iso.refl (R₂ ⋙ R₁)) c).hom.app
      ((L₂.mapHomotopyCategory c).obj
        ((L₁.mapHomotopyCategory c).obj ((HomotopyCategory.quotient C c).obj X))) =
      (HomotopyCategory.quotient C c).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (R₂ ⋙ R₁)) c).hom.app
          ((L₂.mapHomologicalComplex c).obj ((L₁.mapHomologicalComplex c).obj X))) := rfl
  rw [mapHomotopyCategory_unit_app_quotient, mapHomotopyCategory_unit_app_quotient,
    h₂, hmapR₁, hciR, hciL, hmapR, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    ← mapHomologicalComplex_comp_unit_app]

end Localization

section Plus

variable [Limits.HasBinaryBiproducts C] [Limits.HasBinaryBiproducts D]
  [Limits.HasBinaryBiproducts E]

/-- The unit of `Adjunction.mapHomotopyCategoryPlus` is the restriction of the unit of
`Adjunction.mapHomotopyCategory` along the inclusion of the bounded below subcategory. -/
@[simp]
lemma ι_map_mapHomotopyCategoryPlus_unit_app {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.Additive] [R.Additive] (K : HomotopyCategory.Plus C) :
    (HomotopyCategory.Plus.ι C).map (adj.mapHomotopyCategoryPlus.unit.app K) =
      (adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app K.obj := by
  rw [Adjunction.mapHomotopyCategoryPlus, Adjunction.map_restrictFullyFaithful_unit_app]
  simp

/-- The counit of `Adjunction.mapHomotopyCategoryPlus` is the restriction of the counit of
`Adjunction.mapHomotopyCategory` along the inclusion of the bounded below subcategory. -/
@[simp]
lemma ι_map_mapHomotopyCategoryPlus_counit_app {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.Additive] [R.Additive] (K : HomotopyCategory.Plus D) :
    (HomotopyCategory.Plus.ι D).map (adj.mapHomotopyCategoryPlus.counit.app K) =
      (adj.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app K.obj := by
  dsimp only [Adjunction.mapHomotopyCategoryPlus]
  erw [Adjunction.map_restrictFullyFaithful_counit_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  exact Category.id_comp _

/-- **The identity law for `Adjunction.mapHomotopyCategoryPlus`**: the unit of the
adjunction induced by `Adjunction.id` is the inverse of
`Functor.mapHomotopyCategoryPlusIdIso` followed by the image of that inverse under
`(𝟭 C).mapHomotopyCategoryPlus`. -/
lemma mapHomotopyCategoryPlus_id_unit_app (K : HomotopyCategory.Plus C) :
    (Adjunction.id (C := C)).mapHomotopyCategoryPlus.unit.app K =
      (Functor.mapHomotopyCategoryPlusIdIso C).inv.app K ≫
        (𝟭 C).mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusIdIso C).inv.app K) := by
  apply (HomotopyCategory.Plus.ι C).map_injective
  have hmap : ∀ {A B : HomotopyCategory.Plus C} (f : A ⟶ B),
      (HomotopyCategory.Plus.ι C).map ((𝟭 C).mapHomotopyCategoryPlus.map f) =
        ((𝟭 C).mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.Plus.ι C).map f) := fun _ => rfl
  rw [ι_map_mapHomotopyCategoryPlus_unit_app, Functor.map_comp, hmap,
    Functor.ι_map_mapHomotopyCategoryPlusIdIso_inv_app,
    mapHomotopyCategory_id_unit_app]

/-- The unit of the adjunction induced by `Adjunction.id` is the identity: the sharp form
of `Adjunction.mapHomotopyCategoryPlus_id_unit_app`, since both factors of the composite
appearing there are built from the inverse of `Functor.mapHomotopyCategoryPlusIdIso`, which
is itself an identity (`Functor.mapHomotopyCategoryPlusIdIso_inv_app_eq_id`). -/
@[simp]
lemma mapHomotopyCategoryPlus_id_unit_app_eq_id (K : HomotopyCategory.Plus C) :
    (Adjunction.id (C := C)).mapHomotopyCategoryPlus.unit.app K = 𝟙 K := by
  rw [mapHomotopyCategoryPlus_id_unit_app,
    Functor.mapHomotopyCategoryPlusIdIso_inv_app_eq_id]
  simp

/-- **The composition law for `Adjunction.mapHomotopyCategoryPlus`**: the unit of the
adjunction induced by a composite of adjunctions is the composite of the two units,
transported along `Functor.mapHomotopyCategoryPlusCompIso`. -/
lemma mapHomotopyCategoryPlus_comp_unit_app {L₁ : C ⥤ D} {R₁ : D ⥤ C} (adj₁ : L₁ ⊣ R₁)
    {L₂ : D ⥤ E} {R₂ : E ⥤ D} (adj₂ : L₂ ⊣ R₂)
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive] (K : HomotopyCategory.Plus C) :
    (adj₁.comp adj₂).mapHomotopyCategoryPlus.unit.app K =
      adj₁.mapHomotopyCategoryPlus.unit.app K ≫
        R₁.mapHomotopyCategoryPlus.map (adj₂.mapHomotopyCategoryPlus.unit.app
          (L₁.mapHomotopyCategoryPlus.obj K)) ≫
        (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (R₂ ⋙ R₁))).hom.app
          (L₂.mapHomotopyCategoryPlus.obj (L₁.mapHomotopyCategoryPlus.obj K)) ≫
        (R₂ ⋙ R₁).mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (L₁ ⋙ L₂))).hom.app K) := by
  apply (HomotopyCategory.Plus.ι C).map_injective
  have hmapR₁ : ∀ {A B : HomotopyCategory.Plus D} (f : A ⟶ B),
      (HomotopyCategory.Plus.ι C).map (R₁.mapHomotopyCategoryPlus.map f) =
        (R₁.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.Plus.ι D).map f) := fun _ => rfl
  have hmapR : ∀ {A B : HomotopyCategory.Plus E} (f : A ⟶ B),
      (HomotopyCategory.Plus.ι C).map ((R₂ ⋙ R₁).mapHomotopyCategoryPlus.map f) =
        ((R₂ ⋙ R₁).mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.Plus.ι E).map f) := fun _ => rfl
  have hciL : (HomotopyCategory.Plus.ι E).map
      ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (L₁ ⋙ L₂))).hom.app K) =
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (L₁ ⋙ L₂)) (ComplexShape.up ℤ)).hom.app
        K.obj := rfl
  have hciR : (HomotopyCategory.Plus.ι C).map
      ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (R₂ ⋙ R₁))).hom.app
        (L₂.mapHomotopyCategoryPlus.obj (L₁.mapHomotopyCategoryPlus.obj K))) =
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (R₂ ⋙ R₁)) (ComplexShape.up ℤ)).hom.app
        ((L₂.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((L₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj K.obj)) := rfl
  have h₂ : (HomotopyCategory.Plus.ι D).map (adj₂.mapHomotopyCategoryPlus.unit.app
      (L₁.mapHomotopyCategoryPlus.obj K)) =
      (adj₂.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
        ((L₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj K.obj) :=
    ι_map_mapHomotopyCategoryPlus_unit_app adj₂ _
  rw [ι_map_mapHomotopyCategoryPlus_unit_app, Functor.map_comp, Functor.map_comp,
    Functor.map_comp, ι_map_mapHomotopyCategoryPlus_unit_app, hmapR₁, h₂, hciR, hmapR, hciL,
    mapHomotopyCategory_comp_unit_app]

end Plus

section Conjugate

variable {LA LB : C ⥤ D} {RA RB : D ⥤ C} [LA.Additive] [RA.Additive] [LB.Additive]
  [RB.Additive] (adjA : LA ⊣ RA) (adjB : LB ⊣ RB) (u : LA ⟶ LB) (l : RB ⟶ RA)
  (h : ∀ M, adjA.unit.app M ≫ RA.map (u.app M) = adjB.unit.app M ≫ l.app (LB.obj M))

include h in
/-- Transport to complexes of the unit relation between two adjunctions `LA ⊣ RA`,
`LB ⊣ RB` between the same pair of categories and conjugate transformations `u : LA ⟶ LB`,
`l : RB ⟶ RA`, that is, the commutativity of
```
            adjA.unit
     M ----------------> RA (LA M)
     |                       |
     | adjB.unit             | RA (u)
     v                       v
 RB (LB M) --- l ------> RA (LB M)
```
The units of `Adjunction.mapHomologicalComplex` satisfy the same relation, since they are
given degreewise by the units of `adjA` and `adjB`. -/
lemma mapHomologicalComplex_unit_app_comp (M : HomologicalComplex C c) :
    (adjA.mapHomologicalComplex c).unit.app M ≫
        (RA.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex u c).app M) =
      (adjB.mapHomologicalComplex c).unit.app M ≫
        (NatTrans.mapHomologicalComplex l c).app
          ((LB.mapHomologicalComplex c).obj M) := by
  ext n
  exact h (M.X n)

section

variable [(HomotopyCategory.quotient C c).IsLocalization
    (HomologicalComplex.homotopyEquivalences C c)]
  [(HomotopyCategory.quotient D c).IsLocalization
    (HomologicalComplex.homotopyEquivalences D c)]

include h in
/-- The homotopy category form of `Adjunction.mapHomologicalComplex_unit_app_comp`. -/
lemma mapHomotopyCategory_unit_app_comp (Z : HomotopyCategory C c) :
    (adjA.mapHomotopyCategory c).unit.app Z ≫
        (RA.mapHomotopyCategory c).map ((NatTrans.mapHomotopyCategory u c).app Z) =
      (adjB.mapHomotopyCategory c).unit.app Z ≫
        (NatTrans.mapHomotopyCategory l c).app
          ((LB.mapHomotopyCategory c).obj Z) := by
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  have hu : (NatTrans.mapHomotopyCategory u c).app
      ((HomotopyCategory.quotient C c).obj M) =
      (HomotopyCategory.quotient D c).map
        ((NatTrans.mapHomologicalComplex u c).app M) := rfl
  have hl : (NatTrans.mapHomotopyCategory l c).app
      ((LB.mapHomotopyCategory c).obj ((HomotopyCategory.quotient C c).obj M)) =
      (HomotopyCategory.quotient C c).map
        ((NatTrans.mapHomologicalComplex l c).app
          ((LB.mapHomologicalComplex c).obj M)) := rfl
  have hmapR : ∀ {P Q : HomologicalComplex D c} (g : P ⟶ Q),
      (RA.mapHomotopyCategory c).map ((HomotopyCategory.quotient D c).map g) =
        (HomotopyCategory.quotient C c).map ((RA.mapHomologicalComplex c).map g) :=
    fun _ => rfl
  rw [mapHomotopyCategory_unit_app_quotient, mapHomotopyCategory_unit_app_quotient, hu, hl,
    hmapR, ← Functor.map_comp, ← Functor.map_comp,
    mapHomologicalComplex_unit_app_comp c adjA adjB u l h]

end

include h in
/-- **The bounded below homotopy category form of
`Adjunction.mapHomologicalComplex_unit_app_comp`**: if `u : LA ⟶ LB` and `l : RB ⟶ RA`
satisfy the unit relation `adjA.unit ≫ RA(u) = adjB.unit ≫ l` for two adjunctions
`LA ⊣ RA`, `LB ⊣ RB` between the same pair of categories, then so do the transformations
they induce on the bounded below homotopy categories. -/
lemma mapHomotopyCategoryPlus_unit_app_comp [Limits.HasBinaryBiproducts C]
    [Limits.HasBinaryBiproducts D] (K : HomotopyCategory.Plus C) :
    adjA.mapHomotopyCategoryPlus.unit.app K ≫
        RA.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus u).app K) =
      adjB.mapHomotopyCategoryPlus.unit.app K ≫
        (NatTrans.mapHomotopyCategoryPlus l).app
          (LB.mapHomotopyCategoryPlus.obj K) := by
  apply (HomotopyCategory.Plus.ι C).map_injective
  have hmapR : ∀ {P Q : HomotopyCategory.Plus D} (g : P ⟶ Q),
      (HomotopyCategory.Plus.ι C).map (RA.mapHomotopyCategoryPlus.map g) =
        (RA.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.Plus.ι D).map g) := fun _ => rfl
  have hu : (HomotopyCategory.Plus.ι D).map
      ((NatTrans.mapHomotopyCategoryPlus u).app K) =
      (NatTrans.mapHomotopyCategory u (ComplexShape.up ℤ)).app
        ((HomotopyCategory.Plus.ι C).obj K) := rfl
  have hl : (HomotopyCategory.Plus.ι C).map
      ((NatTrans.mapHomotopyCategoryPlus l).app (LB.mapHomotopyCategoryPlus.obj K)) =
      (NatTrans.mapHomotopyCategory l (ComplexShape.up ℤ)).app
        ((LB.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.Plus.ι C).obj K)) := rfl
  rw [Functor.map_comp, Functor.map_comp, hmapR, hu, hl,
    ι_map_mapHomotopyCategoryPlus_unit_app, ι_map_mapHomotopyCategoryPlus_unit_app]
  exact mapHomotopyCategory_unit_app_comp (ComplexShape.up ℤ) adjA adjB u l h K.obj

end Conjugate

section ConjugateWhisker

variable {E : Type*} [Category* E] [Preadditive E] {LA : C ⥤ D} {RA : D ⥤ C} {LB : C ⥤ E}
  {RB : E ⥤ C} {H : E ⥤ D} [LA.Additive] [RA.Additive] [LB.Additive] [RB.Additive] [H.Additive]
  (adjA : LA ⊣ RA) (adjB : LB ⊣ RB) (u : LA ⟶ LB ⋙ H) (l : RB ⟶ H ⋙ RA)
  (h : ∀ M, adjA.unit.app M ≫ RA.map (u.app M) = adjB.unit.app M ≫ l.app (LB.obj M))

include h in
/-- The variant of `Adjunction.mapHomologicalComplex_unit_app_comp` for adjunctions `LA ⊣ RA`,
`LB ⊣ RB` with different targets, related by a functor `H` and transformations
`u : LA ⟶ LB ⋙ H`, `l : RB ⟶ H ⋙ RA` satisfying `adjA.unit ≫ RA(u) = adjB.unit ≫ l`. -/
lemma mapHomologicalComplex_unit_app_comp_whisker (M : HomologicalComplex C c) :
    (adjA.mapHomologicalComplex c).unit.app M ≫
        (RA.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex u c).app M) =
      (adjB.mapHomologicalComplex c).unit.app M ≫
        (NatTrans.mapHomologicalComplex l c).app ((LB.mapHomologicalComplex c).obj M) := by
  ext n
  exact h (M.X n)

include h in
/-- The homotopy category form of `Adjunction.mapHomologicalComplex_unit_app_comp_whisker`. -/
lemma mapHomotopyCategory_unit_app_comp_whisker
    [(HomotopyCategory.quotient C c).IsLocalization
      (HomologicalComplex.homotopyEquivalences C c)]
    [(HomotopyCategory.quotient D c).IsLocalization
      (HomologicalComplex.homotopyEquivalences D c)]
    [(HomotopyCategory.quotient E c).IsLocalization
      (HomologicalComplex.homotopyEquivalences E c)]
    (Z : HomotopyCategory C c) :
    (adjA.mapHomotopyCategory c).unit.app Z ≫
        (RA.mapHomotopyCategory c).map ((NatTrans.mapHomotopyCategory u c).app Z) =
      (adjB.mapHomotopyCategory c).unit.app Z ≫
        (NatTrans.mapHomotopyCategory l c).app ((LB.mapHomotopyCategory c).obj Z) := by
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  have hu : (NatTrans.mapHomotopyCategory u c).app ((HomotopyCategory.quotient C c).obj M) =
      (HomotopyCategory.quotient D c).map ((NatTrans.mapHomologicalComplex u c).app M) := rfl
  have hl : (NatTrans.mapHomotopyCategory l c).app
      ((LB.mapHomotopyCategory c).obj ((HomotopyCategory.quotient C c).obj M)) =
      (HomotopyCategory.quotient C c).map
        ((NatTrans.mapHomologicalComplex l c).app ((LB.mapHomologicalComplex c).obj M)) := rfl
  have hmapR : ∀ {P Q : HomologicalComplex D c} (g : P ⟶ Q),
      (RA.mapHomotopyCategory c).map ((HomotopyCategory.quotient D c).map g) =
        (HomotopyCategory.quotient C c).map ((RA.mapHomologicalComplex c).map g) :=
    fun _ => rfl
  rw [mapHomotopyCategory_unit_app_quotient, mapHomotopyCategory_unit_app_quotient, hu, hl,
    hmapR, ← Functor.map_comp, ← Functor.map_comp,
    mapHomologicalComplex_unit_app_comp_whisker c adjA adjB u l h]

include h in
/-- The bounded below homotopy category form of
`Adjunction.mapHomologicalComplex_unit_app_comp_whisker`. -/
lemma mapHomotopyCategoryPlus_unit_app_comp_whisker [Limits.HasBinaryBiproducts C]
    [Limits.HasBinaryBiproducts D] [Limits.HasBinaryBiproducts E]
    (K : HomotopyCategory.Plus C) :
    adjA.mapHomotopyCategoryPlus.unit.app K ≫
        RA.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus u).app K) =
      adjB.mapHomotopyCategoryPlus.unit.app K ≫
        (NatTrans.mapHomotopyCategoryPlus l).app (LB.mapHomotopyCategoryPlus.obj K) := by
  apply (HomotopyCategory.Plus.ι C).map_injective
  have hmapR : ∀ {P Q : HomotopyCategory.Plus D} (g : P ⟶ Q),
      (HomotopyCategory.Plus.ι C).map (RA.mapHomotopyCategoryPlus.map g) =
        (RA.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.Plus.ι D).map g) := fun _ => rfl
  have hu : (HomotopyCategory.Plus.ι D).map ((NatTrans.mapHomotopyCategoryPlus u).app K) =
      (NatTrans.mapHomotopyCategory u (ComplexShape.up ℤ)).app
        ((HomotopyCategory.Plus.ι C).obj K) := rfl
  have hl : (HomotopyCategory.Plus.ι C).map
      ((NatTrans.mapHomotopyCategoryPlus l).app (LB.mapHomotopyCategoryPlus.obj K)) =
      (NatTrans.mapHomotopyCategory l (ComplexShape.up ℤ)).app
        ((LB.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.Plus.ι C).obj K)) := rfl
  rw [Functor.map_comp, Functor.map_comp, hmapR, hu, hl,
    ι_map_mapHomotopyCategoryPlus_unit_app, ι_map_mapHomotopyCategoryPlus_unit_app]
  exact mapHomotopyCategory_unit_app_comp_whisker (ComplexShape.up ℤ) adjA adjB u l h K.obj

end ConjugateWhisker

section ConjugateId

variable {L R : C ⥤ C} [L.Additive] [R.Additive] (adj : L ⊣ R) (u : L ≅ 𝟭 C) (l : R ≅ 𝟭 C)
  (h : ∀ M, adj.unit.app M ≫ R.map (u.hom.app M) = l.inv.app M)

include h in
/-- The special case `adjB = Adjunction.id` of
`Adjunction.mapHomotopyCategoryPlus_unit_app_comp`: an adjunction `L ⊣ R` of endofunctors
with isomorphisms `u : L ≅ 𝟭`, `l : R ≅ 𝟭` satisfying `adj.unit ≫ R(u) = l⁻¹`. -/
lemma mapHomotopyCategoryPlus_unit_app_comp_id [Limits.HasBinaryBiproducts C]
    (K : HomotopyCategory.Plus C) :
    adj.mapHomotopyCategoryPlus.unit.app K ≫
        R.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus u.hom).app K) =
      (NatTrans.mapHomotopyCategoryPlus l.inv).app K := by
  have h' : ∀ M, adj.unit.app M ≫ R.map (u.hom.app M) =
      (Adjunction.id (C := C)).unit.app M ≫ l.inv.app ((𝟭 C).obj M) := by
    intro M
    simpa using h M
  rw [mapHomotopyCategoryPlus_unit_app_comp adj (Adjunction.id (C := C)) u.hom l.inv h' K,
    mapHomotopyCategoryPlus_id_unit_app_eq_id]
  exact Category.id_comp _

end ConjugateId

end Adjunction

namespace NatTrans

variable {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Preadditive C₁] [Preadditive C₂] [Preadditive C₃] [Preadditive C₄]
  [Limits.HasBinaryBiproducts C₁] [Limits.HasBinaryBiproducts C₂]
  [Limits.HasBinaryBiproducts C₃] [Limits.HasBinaryBiproducts C₄]
  {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
  {G : C₂ ⥤ C₄} {G' : C₁ ⥤ C₃}
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [G'.Additive]

/-- **Mates on the bounded below homotopy categories.** For adjunctions `L ⊣ R` and
`L' ⊣ R'` and a square `σ : G ⋙ L' ⟶ L ⋙ G'`, the transformation induced on the bounded below
homotopy categories by the mate `R ⋙ G ⟶ G' ⋙ R'` of `σ` is the mate of the induced square
with respect to the induced adjunctions `Adjunction.mapHomotopyCategoryPlus`: both are computed
degreewise on complexes. -/
lemma mapHomotopyCategoryPlus_mateEquiv_app (adj : L ⊣ R) (adj' : L' ⊣ R')
    (σ : TwoSquare G L L' G') (K : HomotopyCategory.Plus C₁) :
    (NatTrans.mapHomotopyCategoryPlus (mateEquiv adj adj' σ)).app K =
      adj'.mapHomotopyCategoryPlus.unit.app (G.mapHomotopyCategoryPlus.obj
          (R.mapHomotopyCategoryPlus.obj K)) ≫
        R'.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus σ).app
          (R.mapHomotopyCategoryPlus.obj K)) ≫
        R'.mapHomotopyCategoryPlus.map (G'.mapHomotopyCategoryPlus.map
          (adj.mapHomotopyCategoryPlus.counit.app K)) := by
  apply (HomotopyCategory.Plus.ι C₄).map_injective
  obtain ⟨⟨X⟩, hK⟩ := K
  rw [ι_map_mapHomotopyCategoryPlus_app]
  erw [Functor.map_comp, Functor.map_comp, Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app]
  have e₁ : ∀ {M N : HomotopyCategory.Plus C₃} (φ : M ⟶ N),
      (HomotopyCategory.Plus.ι C₄).map (R'.mapHomotopyCategoryPlus.map φ) =
        (R'.mapHomotopyCategory (ComplexShape.up ℤ)).map ((HomotopyCategory.Plus.ι C₃).map φ) :=
    fun _ => rfl
  have e₂ : ∀ {M N : HomotopyCategory.Plus C₁} (φ : M ⟶ N),
      (HomotopyCategory.Plus.ι C₃).map (G'.mapHomotopyCategoryPlus.map φ) =
        (G'.mapHomotopyCategory (ComplexShape.up ℤ)).map ((HomotopyCategory.Plus.ι C₁).map φ) :=
    fun _ => rfl
  erw [e₁, e₁, e₂, ι_map_mapHomotopyCategoryPlus_app,
    Adjunction.ι_map_mapHomotopyCategoryPlus_counit_app]
  change _ = (Adjunction.mapHomotopyCategory (ComplexShape.up ℤ) adj').unit.app
    ((HomotopyCategory.quotient C₄ (ComplexShape.up ℤ)).obj _) ≫ _ ≫
      (R'.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((G'.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((Adjunction.mapHomotopyCategory (ComplexShape.up ℤ) adj).counit.app
            ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj X)))
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  change (HomotopyCategory.quotient C₄ (ComplexShape.up ℤ)).map _ =
    (HomotopyCategory.quotient C₄ (ComplexShape.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C₄ (ComplexShape.up ℤ)).map _ ≫
        (HomotopyCategory.quotient C₄ (ComplexShape.up ℤ)).map _
  erw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n
  simp only [mateEquiv_apply, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Adjunction.mapHomologicalComplex_unit_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f, NatTrans.comp_app, Functor.comp_obj,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp, Functor.comp_map, Functor.map_comp]
  exact congrArg (fun t => _ ≫ _ ≫ t) (Category.comp_id _)

end NatTrans

end CategoryTheory
