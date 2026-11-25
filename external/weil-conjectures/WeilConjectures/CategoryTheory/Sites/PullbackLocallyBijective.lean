/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback

/-!
# Recognizing adjoint transposes for the sheaf pullback as isomorphisms

Let `G : C ⥤ D` be a continuous functor between sites `(C, J)` and `(D, K)`, `F` a sheaf on `C`
and `H` a sheaf on `D`. The sheaf pullback `G^* F` of
`Functor.sheafPullbackConstruction.sheafPullback` is the sheafification of the left Kan extension
`G.op.lan.obj F`, and a morphism `φ : F ⟶ G_* H` has an adjoint transpose `G^* F ⟶ H`. This file
shows that the adjoint transpose is an isomorphism as soon as the underlying morphism of
presheaves `G.op.lan.obj F ⟶ H`, the transpose of `φ` for the Kan extension adjunction, is
locally injective and locally surjective
(`CategoryTheory.Functor.sheafPullbackConstruction.isIso_homEquiv_symm_of_isLocallyBijective`).

It also records two descriptions of the left Kan extension used to check this in practice:
every section of the pointwise left Kan extension along the opposite of a representably flat
functor is the image of a single section along a single structure morphism
(`CategoryTheory.Functor.exists_leftKanExtensionUnit_app_eq`), and the value of the transpose on
such a section
(`Functor.leftKanExtensionUnit_app_comp_map_comp_lanAdjunction_homEquiv_symm_app`).
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

/-- The adjoint transposes of a morphism `f : X ⟶ G.obj Y` for two left adjoints of the same
functor `G` differ by the comparison isomorphism `Adjunction.leftAdjointUniq`. -/
lemma Adjunction.homEquiv_symm_eq_leftAdjointUniq_hom_app_comp {C D : Type*} [Category* C]
    [Category* D] {F F' : C ⥤ D} {G : D ⥤ C} (adj₁ : F ⊣ G) (adj₂ : F' ⊣ G) {X : C} {Y : D}
    (f : X ⟶ G.obj Y) :
    (adj₁.homEquiv X Y).symm f =
      (leftAdjointUniq adj₁ adj₂).hom.app X ≫ (adj₂.homEquiv X Y).symm f := by
  rw [Equiv.symm_apply_eq, Adjunction.homEquiv_unit, Functor.map_comp,
    unit_leftAdjointUniq_hom_app_assoc, ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]

/-- Whether the adjoint transpose of a morphism `f : X ⟶ G.obj Y` is an isomorphism does not
depend on the choice of the left adjoint of `G`. -/
lemma Adjunction.isIso_homEquiv_symm_iff {C D : Type*} [Category* C]
    [Category* D] {F F' : C ⥤ D} {G : D ⥤ C} (adj₁ : F ⊣ G) (adj₂ : F' ⊣ G) {X : C} {Y : D}
    (f : X ⟶ G.obj Y) :
    IsIso ((adj₁.homEquiv X Y).symm f) ↔ IsIso ((adj₂.homEquiv X Y).symm f) := by
  rw [homEquiv_symm_eq_leftAdjointUniq_hom_app_comp adj₁ adj₂]
  exact isIso_comp_left_iff _ _

section KanExtension

variable {C D H : Type*} [Category* C] [Category* D] [Category* H]

/-- The transpose `θ : L.lan.obj P ⟶ Q` of `φ : P ⟶ L ⋙ Q` for the adjunction `L.lan ⊣ L ⋙ -`
sends the image of a section `x` of `P` over `X` along `f : L.obj X ⟶ Y` to the image of
`φ x` along `f`. -/
@[reassoc]
lemma Functor.leftKanExtensionUnit_app_comp_map_comp_lanAdjunction_homEquiv_symm_app
    (L : C ⥤ D) [∀ P : C ⥤ H, L.HasLeftKanExtension P] {P : C ⥤ H} {Q : D ⥤ H}
    (φ : P ⟶ L ⋙ Q) {X : C} {Y : D} (f : L.obj X ⟶ Y) :
    (L.leftKanExtensionUnit P).app X ≫ (L.leftKanExtension P).map f ≫
        (((L.lanAdjunction H).homEquiv P Q).symm φ).app Y =
      φ.app X ≫ Q.map f := by
  have h := congr_app (((L.lanAdjunction H).homEquiv P Q).apply_symm_apply φ) X
  rw [Adjunction.homEquiv_unit, lanAdjunction_unit] at h
  rw [NatTrans.naturality, ← h]
  simp [lanUnit]

variable {FH : H → H → Type*} {CH : H → Type*} [∀ X Y, FunLike (FH X Y) (CH X) (CH Y)]
  [ConcreteCategory H FH]

/-- Every section over `Y` of the pointwise left Kan extension of a presheaf `P` along the
opposite of a functor `F` is the image of a section `x` of `P` over some `X` along some
`ψ : Y ⟶ F.obj X`, provided the forgetful functor preserves the colimits over the costructured
arrows computing the Kan extension (e.g. if `F` is representably flat, so that these are
filtered colimits, and the forgetful functor preserves filtered colimits). -/
lemma Functor.exists_leftKanExtensionUnit_app_eq (F : C ⥤ D) (P : Cᵒᵖ ⥤ H)
    [F.op.HasPointwiseLeftKanExtension P] {Y : D}
    [PreservesColimitsOfShape (CostructuredArrow F.op (op Y)) (forget H)]
    (y : ToType ((F.op.leftKanExtension P).obj (op Y))) :
    ∃ (X : C) (ψ : Y ⟶ F.obj X) (x : ToType (P.obj (op X))),
      (F.op.leftKanExtension P).map ψ.op ((F.op.leftKanExtensionUnit P).app (op X) x) = y := by
  obtain ⟨j, x, rfl⟩ := Concrete.isColimit_exists_rep _
    (F.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit P (op Y)) y
  refine ⟨j.left.unop, j.hom.unop, x, ?_⟩
  rw [LeftExtension.coconeAt_ι_app, ConcreteCategory.comp_apply]
  rfl

end KanExtension

namespace Functor.sheafPullbackConstruction

variable {C D : Type*} [Category* C] [Category* D]
    (G : C ⥤ D) (A : Type*) [Category* A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [G.IsContinuous J K] [HasWeakSheafify K A] [∀ (P : Cᵒᵖ ⥤ A), G.op.HasLeftKanExtension P]

/-- The unit of the adjunction `G^* ⊣ G_*` is the unit of the left Kan extension followed by
the sheafification map. -/
lemma sheafAdjunctionContinuous_unit_app_hom (F : Sheaf J A) :
    ((sheafAdjunctionContinuous G A J K).unit.app F).hom =
      G.op.lanUnit.app F.obj ≫ G.op.whiskerLeft (toSheafify K (G.op.lan.obj F.obj)) := by
  dsimp [sheafAdjunctionContinuous]
  rw [← sheafToPresheaf_map, Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [lan, ObjectProperty.ι_obj, Functor.id_obj, Adjunction.comp_unit_app,
    lanAdjunction_unit, sheafificationAdjunction_unit_app, whiskeringLeft_obj_map, Iso.refl_hom,
    NatTrans.id_app, Functor.comp_map, ObjectProperty.ι_map,
    ObjectProperty.FullSubcategory.id_hom, Category.assoc]
  erw [Functor.whiskerLeft_id', Category.comp_id, Category.comp_id]

/-- The adjoint transpose `G^* F ⟶ H` of `φ : F ⟶ G_* H`, precomposed with the sheafification
map, is the transpose of `φ` for the left Kan extension adjunction. -/
lemma toSheafify_comp_homEquiv_symm_hom
    {F : Sheaf J A} {H : Sheaf K A} (φ : F ⟶ (G.sheafPushforwardContinuous A J K).obj H) :
    toSheafify K (G.op.lan.obj F.obj) ≫
        (((sheafAdjunctionContinuous G A J K).homEquiv F H).symm φ).hom =
      ((G.op.lanAdjunction A).homEquiv F.obj H.obj).symm φ.hom := by
  rw [Equiv.eq_symm_apply, Adjunction.homEquiv_unit, lanAdjunction_unit]
  conv_rhs => rw [← Equiv.apply_symm_apply ((sheafAdjunctionContinuous G A J K).homEquiv F H) φ,
    Adjunction.homEquiv_unit]
  rw [ObjectProperty.FullSubcategory.comp_hom, sheafAdjunctionContinuous_unit_app_hom]
  simp

variable {FA : A → A → Type*} {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
  [ConcreteCategory A FA] [K.WEqualsLocallyBijective A] [(forget A).ReflectsIsomorphisms]
  [K.HasSheafCompose (forget A)]

/-- **Recognizing the sheaf pullback.** The adjoint transpose `G^* F ⟶ H` of `φ : F ⟶ G_* H` is
an isomorphism if the transpose `G.op.lan.obj F ⟶ H` of `φ` for the left Kan extension
adjunction is locally injective and locally surjective. -/
lemma isIso_homEquiv_symm_of_isLocallyBijective
    {F : Sheaf J A} {H : Sheaf K A} (φ : F ⟶ (G.sheafPushforwardContinuous A J K).obj H)
    [Presheaf.IsLocallyInjective K (((G.op.lanAdjunction A).homEquiv F.obj H.obj).symm φ.hom)]
    [Presheaf.IsLocallySurjective K (((G.op.lanAdjunction A).homEquiv F.obj H.obj).symm φ.hom)] :
    IsIso (((sheafAdjunctionContinuous G A J K).homEquiv F H).symm φ) := by
  rw [← Sheaf.isLocallyBijective_iff_isIso (FA := FA)]
  exact ⟨Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac K _
      (toSheafify_comp_homEquiv_symm_hom G A J K φ),
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac K
      (toSheafify_comp_homEquiv_symm_hom G A J K φ)⟩

end Functor.sheafPullbackConstruction

end CategoryTheory
