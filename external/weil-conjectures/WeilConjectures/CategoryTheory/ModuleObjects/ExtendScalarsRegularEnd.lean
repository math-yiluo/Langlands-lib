/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleUpperStar

/-!
# Extension of scalars and the multiplications on the regular module

Let `φ : R ⟶ S` be a morphism of commutative algebra objects. Extension of scalars along `φ`
sends the regular module `R` to the regular module `S` (`Mod.extendScalarsObjRegularIso`), and
under this identification it sends the multiplication by a global section `s : 𝟙 ⟶ R` to the
multiplication by its image `s ≫ φ` (`Mod.extendScalarsObjRegularIso_inv_comp_map`).
-/

@[expose] public section

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ]

/-- The unit `M ⟶ S ⊗_R M` of extension of scalars is natural. -/
@[reassoc]
lemma extendUnitHom_naturality {M N : Mod C R} (f : M ⟶ N) :
    extendUnitHom φ M ≫ ((extendScalars φ).map f).hom = f.hom ≫ extendUnitHom φ N := by
  have h : extendUnitHom φ M ≫ (extendScalarsMap φ f).hom = f.hom ≫ extendUnitHom φ N := by
    dsimp only [extendUnitHom]
    rw [Category.assoc, Category.assoc, extendπ_extendScalarsMap, ← whisker_exchange_assoc,
      ← leftUnitor_inv_naturality_assoc]
  exact h


/-- The inverse of `S ⊗_R R ≅ S` restricted along `φ` is the unit `R ⟶ S ⊗_R R`. -/
@[reassoc]
lemma comp_extendScalarsObjRegularIso_inv_hom :
    φ ≫ (extendScalarsObjRegularIso φ).inv.hom = extendUnitHom φ (regular R) := by
  dsimp only [extendScalarsObjRegularIso]
  rw [regularLift, homMk_hom]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc, whiskerLeft_comp_assoc,
    whiskerLeft_extendUnitHom_smul, ← smul_extendUnitHom]
  erw [MonObj.mul_one_assoc]
  rw [Iso.inv_hom_id_assoc]

/-- The inverse of `S ⊗_R R ≅ S` sends `1` to `1 ⊗ 1`. -/
@[reassoc]
lemma one_comp_extendScalarsObjRegularIso_inv_hom :
    η[S] ≫ (extendScalarsObjRegularIso φ).inv.hom = η[R] ≫ extendUnitHom φ (regular R) := by
  dsimp only [extendScalarsObjRegularIso]
  exact one_comp_regularLift _ _

variable [Preadditive C] [MonoidalPreadditive C] [IsCommMonObj S]

/-- Under `S ⊗_R R ≅ S`, extension of scalars sends the multiplication by a global section
`s : 𝟙 ⟶ R` of `R` to the multiplication by the global section `s ≫ φ` of `S`. -/
@[reassoc]
lemma extendScalarsObjRegularIso_inv_comp_map (s : Γ R) :
    (extendScalarsObjRegularIso φ).inv ≫ (extendScalars φ).map (regularEndRingHom s).asHom =
      (regularEndRingHom (Γ.map φ s)).asHom ≫ (extendScalarsObjRegularIso φ).inv := by
  refine regular_hom_ext ?_
  rw [comp_hom', comp_hom', regularEndRingHom_apply, regularEndRingHom_apply,
    one_comp_extendScalarsObjRegularIso_inv_hom_assoc, extendUnitHom_naturality,
    ← Category.assoc, one_comp_regularLift, ← Category.assoc, one_comp_regularLift,
    Γ.map_hom, Category.assoc, comp_extendScalarsObjRegularIso_inv_hom φ]

variable {T : C} [MonObj T] [IsCommMonObj T] (ψ : S ⟶ T) [IsMonHom ψ]

/-- The extension of scalars of the regular module along a composite `R ⟶ S ⟶ T`:
`T ⊗_S (S ⊗_R R) ≅ T ⊗_S S ≅ T`. -/
noncomputable def extendScalarsCompObjRegularIso :
    (extendScalars φ ⋙ extendScalars ψ).obj (regular R) ≅ regular T :=
  (extendScalars ψ).mapIso (extendScalarsObjRegularIso φ) ≪≫ extendScalarsObjRegularIso ψ

/-- Under `T ⊗_S (S ⊗_R R) ≅ T`, the extensions of scalars along `R ⟶ S ⟶ T` send the
multiplication by a global section `s` of `R` to the multiplication by its image in `T`. -/
lemma extendScalarsCompObjRegularIso_inv_comp_map (s : Γ R) :
    (extendScalarsCompObjRegularIso φ ψ).inv ≫
        (extendScalars φ ⋙ extendScalars ψ).map (regularEndRingHom s).asHom =
      (regularEndRingHom (Γ.map ψ (Γ.map φ s))).asHom ≫
        (extendScalarsCompObjRegularIso φ ψ).inv := by
  rw [extendScalarsCompObjRegularIso, Iso.trans_inv, Functor.mapIso_inv, Functor.comp_map,
    Category.assoc, ← Functor.map_comp, extendScalarsObjRegularIso_inv_comp_map, Functor.map_comp,
    extendScalarsObjRegularIso_inv_comp_map_assoc]

end CategoryTheory.Mod
