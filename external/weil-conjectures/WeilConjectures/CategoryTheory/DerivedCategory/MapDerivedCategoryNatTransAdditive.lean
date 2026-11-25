/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Functoriality and additivity of the derived natural transformations

For exact functors between abelian categories, the natural transformation
`Functor.mapDerivedCategoryNatTrans τ : D(F) ⟶ D(G)` induced by `τ : F ⟶ G` is compatible with
identities, composition, sums and multiples (`Functor.mapDerivedCategoryNatTrans_comp`,
`Functor.mapDerivedCategoryNatTrans_sum`, `Functor.mapDerivedCategoryNatTrans_nsmul`).
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

section

variable {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

lemma mapDerivedCategoryNatTrans_app_Q_obj (τ : F ⟶ G) (K : CochainComplex C ℤ) :
    (mapDerivedCategoryNatTrans τ).app (DerivedCategory.Q.obj K) =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) ≫
          G.mapDerivedCategoryFactors.inv.app K := by
  rw [← mapDerivedCategoryNatTrans_fac_assoc, Iso.hom_inv_id_app]
  exact (comp_id _).symm

@[reassoc]
lemma mapDerivedCategoryNatTrans_comp (τ : F ⟶ G) (τ' : G ⟶ H) :
    mapDerivedCategoryNatTrans (τ ≫ τ') =
      mapDerivedCategoryNatTrans τ ≫ mapDerivedCategoryNatTrans τ' := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) fun K ↦ ?_
  simp only [NatTrans.comp_app, mapDerivedCategoryNatTrans_app_Q_obj, assoc,
    Iso.inv_hom_id_app_assoc, ← DerivedCategory.Q.map_comp_assoc,
    NatTrans.mapHomologicalComplex_comp,
    NatTrans.comp_app]

lemma mapDerivedCategoryNatTrans_id :
    mapDerivedCategoryNatTrans (𝟙 F) = 𝟙 _ := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) fun K ↦ ?_
  simp [mapDerivedCategoryNatTrans_app_Q_obj]

lemma mapDerivedCategoryNatTrans_add (τ τ' : F ⟶ G) :
    mapDerivedCategoryNatTrans (τ + τ') =
      mapDerivedCategoryNatTrans τ + mapDerivedCategoryNatTrans τ' := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) fun K ↦ ?_
  simp only [NatTrans.app_add, mapDerivedCategoryNatTrans_app_Q_obj]
  rw [show (NatTrans.mapHomologicalComplex (τ + τ') (ComplexShape.up ℤ)).app K =
      (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K +
        (NatTrans.mapHomologicalComplex τ' (ComplexShape.up ℤ)).app K by ext n; simp,
    Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

lemma mapDerivedCategoryNatTrans_zero :
    mapDerivedCategoryNatTrans (0 : F ⟶ G) = 0 := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) fun K ↦ ?_
  simp only [mapDerivedCategoryNatTrans_app_Q_obj, NatTrans.app_zero]
  rw [show (NatTrans.mapHomologicalComplex (0 : F ⟶ G) (ComplexShape.up ℤ)).app K = 0 by
    ext n; simp, Functor.map_zero, zero_comp, comp_zero]

/-- `Functor.mapDerivedCategoryNatTrans` as an additive map. -/
noncomputable def mapDerivedCategoryNatTransAddHom :
    (F ⟶ G) →+ (F.mapDerivedCategory ⟶ G.mapDerivedCategory) where
  toFun := mapDerivedCategoryNatTrans
  map_zero' := mapDerivedCategoryNatTrans_zero
  map_add' := mapDerivedCategoryNatTrans_add

lemma mapDerivedCategoryNatTrans_sum {ι : Type*} (s : Finset ι) (τ : ι → (F ⟶ G)) :
    mapDerivedCategoryNatTrans (∑ i ∈ s, τ i) = ∑ i ∈ s, mapDerivedCategoryNatTrans (τ i) :=
  _root_.map_sum mapDerivedCategoryNatTransAddHom τ s

lemma mapDerivedCategoryNatTrans_nsmul (n : ℕ) (τ : F ⟶ G) :
    mapDerivedCategoryNatTrans (n • τ) = n • mapDerivedCategoryNatTrans τ :=
  _root_.map_nsmul mapDerivedCategoryNatTransAddHom n τ

end

end CategoryTheory.Functor
