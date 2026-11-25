/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal

/-!
# The unit of extension of scalars along an isomorphism

Let `φ : R ⟶ S` be a morphism of commutative algebra objects. A morphism out of the extension
of scalars `S ⊗_R M` is determined by its composite with the unit `M ⟶ S ⊗_R M`
(`CategoryTheory.Mod.extendScalarsObj_hom_ext'`). When `φ` is an isomorphism, extension of
scalars along `φ` is restriction of scalars along `φ⁻¹` (`Mod.extendScalarsIsoComapInv`), and
this identification is the identity on underlying objects after the unit
(`CategoryTheory.Mod.extendUnitHom_extendScalarsIsoComapInv_hom_app`).

For a monoidal natural isomorphism `τ : F ⋙ G ⟶ H` of lax monoidal functors, transporting module
objects along `F` and `G` and then extending scalars along `τ_R` is transporting them along `H`
(`CategoryTheory.Functor.mapModCompExtendScalarsIso`). On underlying objects, after the unit, this
comparison is `τ` (`CategoryTheory.Functor.extendUnitHom_mapModCompExtendScalarsIso_hom_app_hom`).

## Main definitions

- `CategoryTheory.Functor.mapModCompExtendScalarsIso`: the comparison
  `mapMod F ⋙ mapMod G ⋙ Ext_{τ_R} ≅ mapMod H`.

## Main results

- `CategoryTheory.Mod.extendScalarsObj_hom_ext'`: morphisms out of `S ⊗_R M` agree if they agree
  after the unit.
- `CategoryTheory.Functor.extendUnitHom_mapModCompExtendScalarsIso_hom_app_hom`: the comparison
  is `τ` after the unit.

## Implementation notes

`CategoryTheory.Functor.extendUnitHom_hom_app_unit_hom_of_eq_mapModCompExtendScalarsIso` takes
an isomorphism `e` together with a proof that it is `Functor.mapModCompExtendScalarsIso`. A
concrete comparison isomorphism defined as the same composite (for instance the comparison of
pullbacks of sheaves of modules `ProEtale.CondensedRing.upperStarFromPointModComp`) should first
be rewritten, by `rfl`, to a reducible copy of the composite, and the lemma applied to that copy.
Applying the lemma to the concrete isomorphism directly makes the kernel compare components
`e.hom.app M` whose implicit arguments differ syntactically; it then unfolds the sheaf pullbacks
and times out.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory

open scoped Obj

namespace Mod

section Comap

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

@[simp]
lemma comapCongr_inv_app_hom {A B : C} [MonObj A] [MonObj B] {f g : A ⟶ B} [IsMonHom f]
    [IsMonHom g] (h : f = g) (M : Mod C B) :
    ((comapCongr h).inv.app M).hom = 𝟙 M.X :=
  rfl

variable {R S : C} [MonObj R] [MonObj S] (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]

/-- The unit of the equivalence given by restriction of scalars along an isomorphism is the
identity on underlying objects. -/
lemma comapEquivalenceOfIsIso_unitIso_inv_app_hom (N : Mod C S) :
    ((comapEquivalenceOfIsIso φ).unitIso.inv.app N).hom = 𝟙 _ := by
  simp only [comapEquivalenceOfIsIso, Equivalence.mk, Equivalence.adjointifyη, Iso.trans_def,
    Iso.trans_symm, Iso.symm_symm_eq, Functor.comp_obj, Functor.id_obj, Iso.trans_assoc,
    Functor.isoWhiskerRight_trans, Functor.isoWhiskerLeft_trans, Iso.trans_inv,
    Functor.isoWhiskerRight_inv, Iso.symm_inv, Category.assoc, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Category.id_comp, comp_hom', comap_map_hom, comapId_inv_app_hom,
    comapCongr_hom_app_hom, comapComp_hom_app_hom, comapComp_inv_app_hom, comapId_hom_app_hom,
    comapCongr_inv_app_hom]
  repeat erw [Category.id_comp]
  rfl

/-- The counit of the equivalence given by restriction of scalars along an isomorphism is the
identity on underlying objects. -/
lemma comapEquivalenceOfIsIso_counitInv_app_hom (N : Mod C R) :
    ((comapEquivalenceOfIsIso φ).counitInv.app N).hom = 𝟙 _ := by
  simp only [Functor.id_obj, comapEquivalenceOfIsIso, Equivalence.mk, Functor.comp_obj,
    Equivalence.Equivalence_mk'_counitInv, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    NatTrans.comp_app, comp_hom', comapId_inv_app_hom, comapCongr_inv_app_hom,
    comapComp_hom_app_hom, Category.id_comp]
  repeat erw [Category.id_comp]

end Comap

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ]

variable {φ} in
/-- Two `S`-linear maps out of `S ⊗_R M` agree if they agree after the unit `M ⟶ S ⊗_R M`. -/
lemma extendScalarsObj_hom_ext' {M : Mod C R} {N : Mod C S} {f g : extendScalarsObj φ M ⟶ N}
    (h : extendUnitHom φ M ≫ f.hom = extendUnitHom φ M ≫ g.hom) : f = g :=
  (extendHomEquiv φ M N).injective (hom_ext _ _ (by
    simp only [extendHomEquiv_apply, comp_hom', extendUnit_hom, comap_map_hom]
    exact h))

/-- The unit `M ⟶ S ⊗_R M` is natural in `M`. -/
@[reassoc]
lemma extendUnitHom_extendScalarsMap {M N : Mod C R} (f : M ⟶ N) :
    extendUnitHom φ M ≫ (extendScalarsMap φ f).hom = f.hom ≫ extendUnitHom φ N := by
  simp only [extendUnitHom, Category.assoc, extendπ_extendScalarsMap]
  rw [← whisker_exchange_assoc, leftUnitor_inv_naturality_assoc]

/-- The unit of the adjunction between extension and restriction of scalars is
`Mod.extendUnitHom` on underlying objects. -/
lemma extendRestrictAdjunction_unit_app_hom (M : Mod C R) :
    ((extendRestrictAdjunction φ).unit.app M).hom = extendUnitHom φ M := by
  simp only [extendRestrictAdjunction, Adjunction.mkOfHomEquiv_unit_app]
  exact Category.comp_id _

section IsIso

variable [IsIso φ]

/-- The identification of extension of scalars along an isomorphism `φ` with restriction of
scalars along `φ⁻¹` is the identity of underlying objects after the unit `M ⟶ S ⊗_R M`. -/
@[reassoc]
lemma extendUnitHom_extendScalarsIsoComapInv_hom_app (M : Mod C R) :
    extendUnitHom φ M ≫ ((extendScalarsIsoComapInv φ).hom.app M).hom = 𝟙 _ := by
  have h := congrArg Mod.Hom.hom (Adjunction.homEquiv_leftAdjointUniq_hom_app
    (extendRestrictAdjunction φ) (comapEquivalenceOfIsIso φ).symm.toAdjunction M)
  have h₂ : ((comapEquivalenceOfIsIso φ).symm.unit.app M).hom = 𝟙 _ :=
    comapEquivalenceOfIsIso_counitInv_app_hom φ M
  rw [Equivalence.toAdjunction_unit, h₂, Adjunction.homEquiv_unit, comp_hom',
    extendRestrictAdjunction_unit_app_hom] at h
  exact h

/-- The isomorphism `Res_φ ⋙ Ext_φ ≅ 𝟭` (extension of scalars being restriction of scalars along
`φ⁻¹`) is the identity of underlying objects after the unit. -/
lemma extendUnitHom_comapExtendScalarsIso_hom_app_hom (N : Mod C S) :
    extendUnitHom φ ((comap φ).obj N) ≫
      ((Functor.isoWhiskerLeft (comap φ) (extendScalarsIsoComapInv φ) ≪≫
        (comapEquivalenceOfIsIso φ).unitIso.symm).hom.app N).hom = 𝟙 _ := by
  change extendUnitHom φ _ ≫ ((extendScalarsIsoComapInv φ).hom.app _ ≫
    (comapEquivalenceOfIsIso φ).unitIso.inv.app N).hom = _
  erw [comp_hom', extendUnitHom_extendScalarsIsoComapInv_hom_app_assoc,
    comapEquivalenceOfIsIso_unitIso_inv_app_hom]
  rfl

end IsIso

end Mod

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- The component of a composite `F ⋙ G ⋙ H ≅ K ⋙ L ⋙ H ≅ K` of a whiskered isomorphism
`a : F ⋙ G ≅ K ⋙ L` and an isomorphism `b : L ⋙ H ≅ 𝟭`, up to associators and unitors: at `x`
it is the composite
```
H (G (F x)) --H (a_x)--> H (L (K x)) --b_{K x}--> K x.
```
-/
lemma associator_symm_trans_isoWhiskerRight_hom_app {A B C' E' : Type*} [Category A] [Category B]
    [Category C'] [Category E'] {F : A ⥤ B} {G : B ⥤ C'} {H : C' ⥤ E'} {K : A ⥤ E'}
    {L : E' ⥤ C'} (a : F ⋙ G ≅ K ⋙ L) (b : L ⋙ H ≅ 𝟭 _) (x : A) :
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight a H ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft K b ≪≫ Functor.rightUnitor K).hom.app x =
      H.map (a.hom.app x) ≫ b.hom.app (K.obj x) := by
  simp

/-- The underlying morphism of `F.mapMod A` of a morphism is `F` of the underlying morphism. -/
lemma mapMod_map_hom (F : C ⥤ D) [F.LaxMonoidal] (A : C) [MonObj A] {M N : Mod C A}
    (g : M ⟶ N) : ((F.mapMod A).map g).hom = F.map g.hom :=
  rfl

variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]
  [HasCoequalizers E] [∀ X : E, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : E, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (F : C ⥤ D) (G : D ⥤ E) {H : C ⥤ E} [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
  (τ : F ⋙ G ⟶ H) [NatTrans.IsMonoidal τ] [IsIso τ] (R : C) [MonObj R]
  [IsCommMonObj (G.obj (F.obj R))] [IsIso (compAlgHom F G τ R)]

/-- Let `τ : F ⋙ G ⟶ H` be a monoidal natural isomorphism. Transporting module objects along `F`
and `G` and then extending scalars along the isomorphism `τ_R : G (F R) ⟶ H R` is transporting
them along `H`: the composite of `Functor.mapModCompIso` with the identification of the extension
of scalars along `τ_R` with a restriction of scalars (`Mod.extendScalarsIsoComapInv`). -/
noncomputable def mapModCompExtendScalarsIso :
    F.mapMod R ⋙ G.mapMod (F.obj R) ⋙ Mod.extendScalars (compAlgHom F G τ R) ≅ H.mapMod R :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (mapModCompIso F G τ R) (Mod.extendScalars (compAlgHom F G τ R)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (Mod.extendScalarsIsoComapInv (compAlgHom F G τ R)) ≪≫
        (Mod.comapEquivalenceOfIsIso (compAlgHom F G τ R)).unitIso.symm) ≪≫
    Functor.rightUnitor _

/-- The comparison `mapMod F ⋙ mapMod G ⋙ Ext_{τ_R} ≅ mapMod H` is `τ` on underlying objects
after the unit `G (F M) ⟶ H R ⊗_{G (F R)} G (F M)`: the square
```
G (F M) ---- unit ----> H R ⊗_{G (F R)} G (F M)
   |                              |
   | τ_M                          | comparison
   v                              v
  H M ============================ H M
```
commutes. -/
lemma extendUnitHom_mapModCompExtendScalarsIso_hom_app_hom (M : Mod C R) :
    Mod.extendUnitHom (compAlgHom F G τ R) ((G.mapMod (F.obj R)).obj ((F.mapMod R).obj M)) ≫
      ((mapModCompExtendScalarsIso F G τ R).hom.app M).hom = τ.app M.X := by
  rw [mapModCompExtendScalarsIso, associator_symm_trans_isoWhiskerRight_hom_app, Mod.comp_hom',
    Mod.extendScalars_map]
  erw [Mod.extendUnitHom_extendScalarsMap_assoc,
    Mod.extendUnitHom_comapExtendScalarsIso_hom_app_hom]
  exact Category.comp_id _

/-- `Functor.extendUnitHom_mapModCompExtendScalarsIso_hom_app_hom` at the unit `R`, for any
isomorphism `e` equal to the comparison `Functor.mapModCompExtendScalarsIso`.

The unit of `Mod C R` is written as the unit of the monoidal category `Mod C R`, the form in which
it occurs in the unit comparisons of monoidal functors. The isomorphism `e` is an argument so that
the lemma applies to a concrete comparison isomorphism without the kernel comparing its components
with those of `Functor.mapModCompExtendScalarsIso`, see the implementation notes of this file. -/
lemma extendUnitHom_hom_app_unit_hom_of_eq_mapModCompExtendScalarsIso [BraidedCategory C]
    [IsCommMonObj R] [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    (e : F.mapMod R ⋙ G.mapMod (F.obj R) ⋙ Mod.extendScalars (compAlgHom F G τ R) ≅ H.mapMod R)
    (he : e = mapModCompExtendScalarsIso F G τ R) :
    Mod.extendUnitHom (compAlgHom F G τ R) ((G.mapMod (F.obj R)).obj ((F.mapMod R).obj
        (@MonoidalCategoryStruct.tensorUnit (Mod C R) _
          MonoidalCategory.toMonoidalCategoryStruct))) ≫
      (e.hom.app
        (@MonoidalCategoryStruct.tensorUnit (Mod C R) _
          MonoidalCategory.toMonoidalCategoryStruct)).hom =
      compAlgHom F G τ R := by
  subst he
  exact extendUnitHom_mapModCompExtendScalarsIso_hom_app_hom F G τ R _

end Functor

end CategoryTheory
