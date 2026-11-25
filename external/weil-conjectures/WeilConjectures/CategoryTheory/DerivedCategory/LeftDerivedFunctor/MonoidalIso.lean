/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidalNatTrans
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformationOplax

/-!
# The comparison isomorphisms of left derived functors are monoidal

Let `F : C ⥤ D` and `G : D ⥤ E` be exact strong monoidal functors between monoidal Grothendieck
abelian categories with functorial flat resolutions, which preserve flat objects and are left
adjoints. Their left derived functors carry the monoidal structures
`CategoryTheory.Functor.leftDerivedFunctorMonoidal`. This file shows:

* the composition isomorphism `L(F ⋙ G) ≅ LF ⋙ LG` is a monoidal natural isomorphism, for the
  monoidal structure of `F ⋙ G` given by composition
  (`CategoryTheory.Functor.isMonoidal_leftDerivedFunctorCompIso_hom`);
* the isomorphism `LF ≅ LF'` induced by a monoidal natural isomorphism `F ≅ F'` is monoidal
  (`CategoryTheory.Functor.isMonoidal_leftDerivedFunctorNatIso_hom`).

The compatibility with the comonoidal structures `δ` is
`CategoryTheory.Functor.map_leftDerivedTensorComparison_app_app_comp` and
`CategoryTheory.Functor.leftDerivedTensorComparison_naturality_app`; the compatibility with the
unit comparisons `η` follows from the description
`CategoryTheory.Functor.leftDerivedFunctorMonoidal_η`
of the unit comparison of `LF` through the counit of `LF` at the unit.
-/

@[expose] public section

universe u u₁ u₂ u₃

open CategoryTheory Category Abelian Limits MonoidalCategory DerivedCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

open LaxMonoidal OplaxMonoidal

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  {E : Type u₃} [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalClosed E] [BraidedCategory E]
  [HasFunctorialFlatResolution E]

section Unit

variable (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso] [F.PreservesFlat]
  [F.IsLeftAdjoint] [F.Monoidal]

/-- The unit comparison of the monoidal functor `LF`, composed with the unit comparison
`𝟙 ⟶ Qh 𝟙` (an isomorphism), is `LF` applied to the unit comparison of `Qh`, followed by the
counit of `LF` at the unit and the unit comparison of `F` on the homotopy categories. -/
lemma leftDerivedFunctorMonoidal_η :
    letI := F.leftDerivedFunctorMonoidal
    η F.leftDerivedFunctor ≫ ε Qh =
      F.leftDerivedFunctor.map (ε Qh) ≫ F.leftDerivedFunctorCounit.app (𝟙_ _) ≫
        Qh.map (η (F.mapHomotopyCategory (.up ℤ))) := by
  have := DerivedCategory.isIso_ε_Qh D
  refine (?_ : (F.leftDerivedFunctor.map (ε Qh) ≫ F.leftDerivedFunctorCounit.app (𝟙_ _) ≫
      Qh.map (η (F.mapHomotopyCategory (.up ℤ))) ≫ CategoryTheory.inv (ε Qh)) ≫ ε Qh = _)
  simp

end Unit

section NatTransComplexes

variable {F F' : C ⥤ D} [F.Additive] [F.IsLeftAdjoint] [F.Monoidal]
  [F'.Additive] [F'.IsLeftAdjoint] [F'.Monoidal]

omit [HasFunctorialFlatResolution C] [HasFunctorialFlatResolution D] [F.IsLeftAdjoint]
  [F'.IsLeftAdjoint] in
/-- A monoidal natural transformation `τ : F ⟶ F'` is compatible with the unit isomorphisms
`𝟙 ≅ F(𝟙)` of the induced monoidal functors on cochain complexes. -/
lemma mapCochainComplexεIso_hom_comp_natTransMapHomologicalComplex_app (τ : F ⟶ F')
    [NatTrans.IsMonoidal τ] :
    F.mapCochainComplexεIso.hom ≫ (NatTrans.mapHomologicalComplex τ (.up ℤ)).app (𝟙_ _) =
      F'.mapCochainComplexεIso.hom := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    mapCochainComplexεIso_hom_f_zero, Category.assoc]
  erw [τ.naturality]
  rw [reassoc_of% (NatTrans.IsMonoidal.unit (τ := τ))]

omit [HasFunctorialFlatResolution C] [HasFunctorialFlatResolution D] in
/-- A monoidal natural transformation `τ : F ⟶ F'` is compatible with the unit comparisons
`F(𝟙) ⟶ 𝟙` of the induced monoidal functors on homotopy categories. -/
lemma natTransMapHomotopyCategory_app_unit_comp_η (τ : F ⟶ F') [NatTrans.IsMonoidal τ] :
    (NatTrans.mapHomotopyCategory τ (.up ℤ)).app (𝟙_ _) ≫ η (F'.mapHomotopyCategory (.up ℤ)) =
      η (F.mapHomotopyCategory (.up ℤ)) := by
  refine (?_ : (HomotopyCategory.quotient D (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app (𝟙_ _)) ≫
        (HomotopyCategory.quotient D (.up ℤ)).map F'.mapCochainComplexεIso.inv =
      (HomotopyCategory.quotient D (.up ℤ)).map F.mapCochainComplexεIso.inv)
  rw [← Functor.map_comp]
  congr 1
  rw [← cancel_epi F.mapCochainComplexεIso.hom,
    reassoc_of% (mapCochainComplexεIso_hom_comp_natTransMapHomologicalComplex_app τ),
    Iso.hom_inv_id, Iso.hom_inv_id]

end NatTransComplexes

section NatIso

variable {F F' : C ⥤ D} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
  [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [F'.PreservesFlat] [F'.IsLeftAdjoint] [F'.Monoidal]

/-- The isomorphism `LF ≅ LF'` induced by a monoidal natural isomorphism `τ : F ≅ F'` is
compatible with the unit comparisons of the monoidal functors `LF` and `LF'`. -/
lemma leftDerivedFunctorNatIso_hom_app_unit_comp_η (τ : F ≅ F') [NatTrans.IsMonoidal τ.hom] :
    letI := F.leftDerivedFunctorMonoidal
    letI := F'.leftDerivedFunctorMonoidal
    (F.leftDerivedFunctorNatIso τ).hom.app (𝟙_ _) ≫ η F'.leftDerivedFunctor =
      η F.leftDerivedFunctor := by
  let := F.leftDerivedFunctorMonoidal
  let := F'.leftDerivedFunctorMonoidal
  have := DerivedCategory.isIso_ε_Qh D
  rw [← cancel_mono (ε Qh), Category.assoc, leftDerivedFunctorMonoidal_η,
    leftDerivedFunctorMonoidal_η, ← NatTrans.naturality_assoc,
    leftDerivedFunctorNatIso_hom_app_comp_counit_assoc, ← Qh.map_comp,
    natTransMapHomotopyCategory_app_unit_comp_η]

/-- The isomorphism `LF ≅ LF'` induced by a monoidal natural isomorphism `τ : F ≅ F'` is a
monoidal natural isomorphism, for the monoidal structures `leftDerivedFunctorMonoidal`. -/
lemma isMonoidal_leftDerivedFunctorNatIso_hom (τ : F ≅ F') [NatTrans.IsMonoidal τ.hom] :
    letI := F.leftDerivedFunctorMonoidal
    letI := F'.leftDerivedFunctorMonoidal
    NatTrans.IsMonoidal (F.leftDerivedFunctorNatIso τ).hom :=
  letI := F.leftDerivedFunctorMonoidal
  letI := F'.leftDerivedFunctorMonoidal
  .of_η_δ _ (leftDerivedFunctorNatIso_hom_app_unit_comp_η τ)
    (fun K M ↦ leftDerivedTensorComparison_naturality_app τ K M)

end NatIso
section Comp

omit [HasFunctorialFlatResolution C] [HasFunctorialFlatResolution D]
  [HasFunctorialFlatResolution E] in
/-- The unit comparison of the composite `F ⋙ G` on homotopy categories is the unit comparison
of `F` followed by the one of `G`. -/
lemma mapHomotopyCategory_map_η_comp_η (F : C ⥤ D) [F.Additive] [F.IsLeftAdjoint] [F.Monoidal]
    (G : D ⥤ E) [G.Additive] [G.IsLeftAdjoint] [G.Monoidal] :
    (G.mapHomotopyCategory (.up ℤ)).map (η (F.mapHomotopyCategory (.up ℤ))) ≫
        η (G.mapHomotopyCategory (.up ℤ)) =
      η ((F ⋙ G).mapHomotopyCategory (.up ℤ)) := by
  have h := mapHomotopyCategoryCompNatTrans_η F G (F ⋙ G) (𝟙 _)
  have e : mapHomotopyCategoryCompNatTrans F G (F ⋙ G) (𝟙 _) (𝟙_ _) = 𝟙 _ := by
    erw [mapHomotopyCategoryCompNatTrans_quotient]
    rw [← Functor.map_id]
    congr 1
    ext n
    rw [mapHomologicalComplexCompNatTrans_f, Functor.map_id]
    rfl
  rw [e, Category.id_comp] at h
  exact h

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
  (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [G.PreservesFlat] [G.IsLeftAdjoint] [G.Monoidal]

/-- The composition isomorphism `L(F ⋙ G) ≅ LF ⋙ LG` is compatible with the unit comparisons of
the monoidal functors `L(F ⋙ G)`, `LF` and `LG`. -/
lemma leftDerivedFunctorCompIso_hom_app_unit_comp_η :
    letI := F.leftDerivedFunctorMonoidal
    letI := G.leftDerivedFunctorMonoidal
    letI := (F ⋙ G).leftDerivedFunctorMonoidal
    (F.leftDerivedFunctorCompIso G).hom.app (𝟙_ _) ≫
        G.leftDerivedFunctor.map (η F.leftDerivedFunctor) ≫ η G.leftDerivedFunctor =
      η (F ⋙ G).leftDerivedFunctor := by
  let := F.leftDerivedFunctorMonoidal
  let := G.leftDerivedFunctorMonoidal
  let := (F ⋙ G).leftDerivedFunctorMonoidal
  have := DerivedCategory.isIso_ε_Qh E
  rw [← cancel_mono (ε Qh), Category.assoc, Category.assoc, leftDerivedFunctorMonoidal_η G,
    ← G.leftDerivedFunctor.map_comp_assoc, leftDerivedFunctorMonoidal_η F,
    leftDerivedFunctorMonoidal_η (F ⋙ G)]
  simp only [Functor.map_comp, Category.assoc]
  erw [G.leftDerivedFunctorCounit.naturality_assoc]
  erw [← (F.leftDerivedFunctorCompIso G).hom.naturality_assoc]
  rw [leftDerivedFunctorCompIso_hom_app_comp_counit_assoc]
  rw [Functor.comp_map, ← Qh.map_comp, mapHomotopyCategory_map_η_comp_η]

/-- The composition isomorphism `L(F ⋙ G) ≅ LF ⋙ LG` is a monoidal natural isomorphism, for the
monoidal structures `leftDerivedFunctorMonoidal` of `LF`, `LG` and `L(F ⋙ G)` (the latter for the
monoidal structure of `F ⋙ G` given by composition). -/
lemma isMonoidal_leftDerivedFunctorCompIso_hom :
    letI := F.leftDerivedFunctorMonoidal
    letI := G.leftDerivedFunctorMonoidal
    letI := (F ⋙ G).leftDerivedFunctorMonoidal
    NatTrans.IsMonoidal (F.leftDerivedFunctorCompIso G).hom := by
  let := F.leftDerivedFunctorMonoidal
  let := G.leftDerivedFunctorMonoidal
  let := (F ⋙ G).leftDerivedFunctorMonoidal
  refine .of_η_δ _ ?_ fun K M ↦ ?_
  · rw [OplaxMonoidal.comp_η]
    exact leftDerivedFunctorCompIso_hom_app_unit_comp_η F G
  · rw [OplaxMonoidal.comp_δ]
    erw [map_leftDerivedTensorComparison_app_app_comp F G K M, Iso.hom_inv_id_app_assoc]
    rfl

/-- For a monoidal natural isomorphism `τ : F ⋙ G ≅ H`, the isomorphism
`LF ⋙ LG ≅ L(F ⋙ G) ≅ LH` is a monoidal natural isomorphism, for the monoidal structures
`leftDerivedFunctorMonoidal`. -/
lemma isMonoidal_leftDerivedFunctorCompIso_symm_trans_natIso_hom
    {H : C ⥤ E} [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [H.PreservesFlat] [H.IsLeftAdjoint] [H.Monoidal] (τ : F ⋙ G ≅ H) [NatTrans.IsMonoidal τ.hom] :
    letI := F.leftDerivedFunctorMonoidal
    letI := G.leftDerivedFunctorMonoidal
    letI := H.leftDerivedFunctorMonoidal
    NatTrans.IsMonoidal
      ((F.leftDerivedFunctorCompIso G).symm ≪≫ (F ⋙ G).leftDerivedFunctorNatIso τ).hom := by
  let := F.leftDerivedFunctorMonoidal
  let := G.leftDerivedFunctorMonoidal
  let := H.leftDerivedFunctorMonoidal
  let := (F ⋙ G).leftDerivedFunctorMonoidal
  have := isMonoidal_leftDerivedFunctorCompIso_hom F G
  have : NatTrans.IsMonoidal (F.leftDerivedFunctorCompIso G).symm.hom :=
    inferInstanceAs (NatTrans.IsMonoidal (F.leftDerivedFunctorCompIso G).inv)
  have := isMonoidal_leftDerivedFunctorNatIso_hom τ
  exact NatTrans.IsMonoidal.comp _ _

end Comp

end CategoryTheory.Functor
