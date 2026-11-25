/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# Counits of mates on homotopy categories

Let `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` be adjunctions of additive functors, `G`, `H`
additive functors and `β : L₁ ⋙ H ≅ G ⋙ L₂` an isomorphism, with mate
`e : R₁ ⋙ G ⟶ H ⋙ R₂` of `β.inv`. The counit relation
`L₂(e) ≫ ε₂ = β⁻¹ ≫ H(ε₁)` of mates still holds for the induced functors and adjunctions on
the homotopy categories (`CategoryTheory.Adjunction.mapHomotopyCategory_map_comp_counit_app`).
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

variable {C₁ D₁ C₂ D₂ : Type*} [Category* C₁] [Category* D₁] [Category* C₂] [Category* D₂]
  [Preadditive C₁] [Preadditive D₁] [Preadditive C₂] [Preadditive D₂]
  {ι : Type*} (c : ComplexShape ι)
  [(HomotopyCategory.quotient C₁ c).IsLocalization (HomologicalComplex.homotopyEquivalences C₁ c)]
  [(HomotopyCategory.quotient D₁ c).IsLocalization (HomologicalComplex.homotopyEquivalences D₁ c)]
  [(HomotopyCategory.quotient C₂ c).IsLocalization (HomologicalComplex.homotopyEquivalences C₂ c)]
  [(HomotopyCategory.quotient D₂ c).IsLocalization (HomologicalComplex.homotopyEquivalences D₂ c)]
  {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂} {G : C₁ ⥤ C₂} {H : D₁ ⥤ D₂}
  [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive] [G.Additive] [H.Additive]

/-- The counit relation of mates, `L₂(e) ≫ ε₂ = β⁻¹ ≫ H(ε₁)` for the mate `e` of `β.inv`, on
homotopy categories, where `L₂(e)` is read through the identifications
`(R₁ ⋙ G).mapHomotopyCategory c = R₁.mapHomotopyCategory c ⋙ G.mapHomotopyCategory c` and the
isomorphism `L₁.mapHomotopyCategory c ⋙ H.mapHomotopyCategory c ≅
G.mapHomotopyCategory c ⋙ L₂.mapHomotopyCategory c` is induced by `β`. -/
lemma mapHomotopyCategory_map_comp_counit_app (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (β : L₁ ⋙ H ≅ G ⋙ L₂) (e : R₁ ⋙ G ⟶ H ⋙ R₂) (he : mateEquiv adj₁ adj₂ β.inv = e)
    (βh : L₁.mapHomotopyCategory c ⋙ H.mapHomotopyCategory c ≅
      G.mapHomotopyCategory c ⋙ L₂.mapHomotopyCategory c)
    (hβh : βh.inv = ((Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ L₂)) c).hom ≫
      NatTrans.mapHomotopyCategory β.inv c) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (L₁ ⋙ H)) c).inv)
    (K : HomotopyCategory D₁ c) :
    (L₂.mapHomotopyCategory c).map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (R₁ ⋙ G)) c).hom.app K ≫
          (NatTrans.mapHomotopyCategory e c).app K ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (H ⋙ R₂)) c).inv.app K) ≫
      (adj₂.mapHomotopyCategory c).counit.app ((H.mapHomotopyCategory c).obj K) =
    βh.inv.app ((R₁.mapHomotopyCategory c).obj K) ≫
      (H.mapHomotopyCategory c).map ((adj₁.mapHomotopyCategory c).counit.app K) := by
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  have hU (d : D₁) : L₂.map (e.app d) ≫ adj₂.counit.app (H.obj d) =
      β.inv.app (R₁.obj d) ≫ H.map (adj₁.counit.app d) := by
    rw [← he]
    exact mateEquiv_counit adj₁ adj₂ β.inv d
  rw [hβh]
  simp only [NatTrans.comp_app, Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryCompIso_refl_inv_app]
  erw [Category.id_comp, Category.id_comp, Category.comp_id, Category.comp_id,
    Adjunction.mapHomotopyCategory_counit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  simp only [NatTrans.mapHomotopyCategory_app, HomotopyCategory.quotient_obj_as]
  erw [Functor.mapHomotopyCategory_map, Functor.mapHomotopyCategory_map, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 1
  refine HomologicalComplex.hom_ext _ _ (fun n ↦ ?_)
  exact hU (X.X n)

end CategoryTheory.Adjunction
