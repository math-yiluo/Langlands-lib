/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.SMulNatTrans

/-!
# Extension of scalars along a free extension with a basis

Let `C` be a braided preadditive monoidal category with finite biproducts and coequalizers
preserved by tensoring, `φ : R ⟶ S` a morphism of commutative algebra objects, and
`t : ι → (𝟙 ⟶ S)` a finite family of global sections of `S` which is a *basis of `S` over `R`*:
the map `⊞_i R ⟶ S`, `(r_i) ↦ Σ φ(r_i) t_i`, is an isomorphism in `C`.

Then for every `R`-module object `M`, the map `M^{⊕ι} ⟶ S ⊗_R M`, `(m_i) ↦ Σ t_i ⊗ m_i`, is an
isomorphism of `R`-module objects (`Mod.isIso_biproductDesc_extendUnit_smul`).

The proof identifies this map with the composite of isomorphisms
`⊞_i M ≅ ⊞_i (R ⊗_R M) ≅ (⊞_i R) ⊗_R M ≅ S ⊗_R M ≅ S ⊗_S (S ⊗_R M) ≅ S ⊗_R M`
given by the left unitors, the distributivity of the relative tensor product over biproducts,
the basis isomorphism (as a map of `R`-modules, `Mod.isIso_biproductDesc_basisHom`) and the
projection formula `Mod.projectionIso`.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

omit [IsCommMonObj S] in
/-- Multiplication by a global section `t` on `S ⊗_R M` on generators: `s ⊗ m ↦ t s ⊗ m`. -/
@[reassoc]
lemma extendπ_smulHom (t : 𝟙_ C ⟶ S) (M : Mod C R) :
    extendπ φ M ≫ smulHom t (extendScalarsObj φ M) =
      ((λ_ S).inv ≫ t ▷ S ≫ μ[S]) ▷ M.X ≫ extendπ φ M := by
  dsimp only [smulHom, act]
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, whiskerLeft_extendπ_smul]
  monoidal

/-- The `R`-linear map `R ⟶ S`, `r ↦ φ(r) t`, for a global section `t : 𝟙 ⟶ S`. -/
noncomputable def basisHom (t : 𝟙_ C ⟶ S) : 𝟙_ (Mod C R) ⟶ (comap φ).obj (𝟙_ (Mod C S)) :=
  comapUnitHom φ ≫ (comap φ).map ((smulNatTrans t).app (𝟙_ (Mod C S)))

/-- The underlying map of `basisHom φ t` is `r ↦ φ(r) t`. -/
lemma basisHom_hom (t : 𝟙_ C ⟶ S) :
    (basisHom φ t).hom = φ ≫ (λ_ S).inv ≫ t ▷ S ≫ μ[S] :=
  rfl

/-- The map `m ↦ t ⊗ m` into `S ⊗_R M` is obtained from `r ↦ φ(r) t` by tensoring with `M` and
the projection formula. -/
lemma extendUnit_comap_map_smulNatTrans_app (t : 𝟙_ C ⟶ S) (M : Mod C R) :
    extendUnit φ M ≫ (comap φ).map ((smulNatTrans t).app ((extendScalars φ).obj M)) =
      (λ_ M).inv ≫ basisHom φ t ▷ M ≫ projectionHom φ (𝟙_ (Mod C S)) M ≫
        (comap φ).map (λ_ (extendScalarsObj φ M)).hom := by
  rw [Iso.eq_inv_comp]
  refine Mod.hom_ext _ _ ?_
  have hl : tensorObjπ (𝟙_ (Mod C R)) M ≫ (λ_ M).hom.hom = γ[R,M.X] :=
    tensorObjπ_regular_leftUnitor_hom M
  rw [← cancel_epi (tensorObjπ (𝟙_ (Mod C R)) M), comp_hom', comp_hom', comp_hom', comp_hom',
    reassoc_of% hl, tensorObjπ_whiskerRight_assoc,
    tensorObjπ_unit_projectionHom_hom_leftUnitor_hom, extendUnit_hom, comap_map_hom,
    smul_extendUnitHom_assoc, smulNatTrans_app_hom, basisHom_hom]
  erw [extendπ_smulHom]
  rw [← comp_whiskerRight_assoc]

variable [Preadditive C] [MonoidalPreadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [HasFiniteBiproducts C]
  {ι : Type} [Finite ι] (t : ι → (𝟙_ C ⟶ S))

/-- If `(r_i) ↦ Σ φ(r_i) t_i` is an isomorphism `⊞_i R ≅ S` in `C`, then it is an isomorphism of
`R`-module objects. -/
lemma isIso_biproductDesc_basisHom
    (hb : IsIso (biproduct.desc fun i : ι ↦ φ ≫ (λ_ S).inv ≫ t i ▷ S ≫ μ[S])) :
    IsIso (biproduct.desc fun i : ι ↦ basisHom φ (t i)) := by
  rw [← isIso_iff_of_reflects_iso _ (forget R), ← biproduct.mapBiproduct_hom_desc]
  exact IsIso.comp_isIso' inferInstance hb

/-- **Extension of scalars along a free extension.** If `S` is free over `R` with basis
`t : ι → (𝟙 ⟶ S)`, i.e. `(r_i) ↦ Σ φ(r_i) t_i` is an isomorphism `⊞_i R ≅ S`, then for every
`R`-module object `M` the map `M^{⊕ι} ⟶ S ⊗_R M`, `(m_i) ↦ Σ t_i ⊗ m_i`, is an isomorphism. -/
theorem isIso_biproductDesc_extendUnit_smul
    (hb : IsIso (biproduct.desc fun i : ι ↦ φ ≫ (λ_ S).inv ≫ t i ▷ S ≫ μ[S])) (M : Mod C R) :
    IsIso (biproduct.desc fun i : ι ↦ (extendRestrictAdjunction φ).unit.app M ≫
      (comap φ).map ((smulNatTrans (t i)).app ((extendScalars φ).obj M))) := by
  have := isIso_biproductDesc_basisHom φ t hb
  have key : (biproduct.desc fun i : ι ↦ (extendRestrictAdjunction φ).unit.app M ≫
      (comap φ).map ((smulNatTrans (t i)).app ((extendScalars φ).obj M))) =
      (biproduct.mapIso fun _ : ι ↦ (λ_ M).symm).hom ≫
        (rightDistributor (fun _ : ι ↦ 𝟙_ (Mod C R)) M).inv ≫
          (biproduct.desc fun i : ι ↦ basisHom φ (t i)) ▷ M ≫
            projectionHom φ (𝟙_ (Mod C S)) M ≫
              (comap φ).map (λ_ (extendScalarsObj φ M)).hom := by
    refine biproduct.hom_ext' _ _ fun i ↦ ?_
    rw [biproduct.ι_desc, biproduct.mapIso_hom, biproduct.ι_map_assoc,
      biproduct_ι_comp_rightDistributor_inv_assoc, ← comp_whiskerRight_assoc, biproduct.ι_desc,
      extendRestrictAdjunction_unit_app]
    exact extendUnit_comap_map_smulNatTrans_app φ (t i) M
  rw [key]
  infer_instance

end CategoryTheory.Mod
