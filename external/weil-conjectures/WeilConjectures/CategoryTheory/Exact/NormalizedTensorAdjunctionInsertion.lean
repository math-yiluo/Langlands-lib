/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroAdjoint
public import WeilConjectures.AlgebraicGeometry.EtaleSingleCochainMonoidal
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Tensor compatibility for representative-normalized adjunction insertions

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-setup/sec-the-purity-statement/sk-thm-purity-transport/sk-thm-purity-transport.proof.md,
Step 1 (compatibility with the finite reductions), the degree-zero scalar calculation.
(blueprint: lem-pur-normalized-tensor-adjunction-insertion)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafExactDegreeZero

private theorem tensor_adjunct
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {U : D ⥤ C} [F.OplaxMonoidal] [U.LaxMonoidal]
    (a : F ⊣ U) [a.IsMonoidal] {M N : C} {P Q : D}
    (f : M ⟶ U.obj P) (g : N ⟶ U.obj Q) :
    Functor.OplaxMonoidal.δ F M N ≫
        ((a.homEquiv _ _).symm f ⊗ₘ (a.homEquiv _ _).symm g) =
      (a.homEquiv _ _).symm ((f ⊗ₘ g) ≫ Functor.LaxMonoidal.μ U P Q) := by
  apply (a.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, a.unit_app_tensor_comp_map_δ, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural]
  rw [tensorHom_comp_tensorHom_assoc]
  change ((a.homEquiv _ _) ((a.homEquiv _ _).symm f) ⊗ₘ
    (a.homEquiv _ _) ((a.homEquiv _ _).symm g)) ≫ _ = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

section Single
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) (U : D ⥤ C) [F.Additive] [U.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (a : F ⊣ U) (E : DerivedCategory C ⥤ DerivedCategory D)
  (ad : E ⊣ U.mapDerivedCategory)

set_option linter.flexible false in
private theorem single_unit_formula (M : C) :
    (ad.homEquiv _ _).symm
      ((DerivedCategory.singleFunctor _ 0).map (a.unit.app M) ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app (F.obj M)) =
    (ad.homEquiv _ _).symm
      (DerivedCategory.Q.map
        ((a.mapHomologicalComplex (.up ℤ)).unit.app
          ((HomologicalComplex.single C (.up ℤ) 0).obj M)) ≫
        U.mapDerivedCategoryFactors.inv.app
          ((F.mapHomologicalComplex (.up ℤ)).obj
            ((HomologicalComplex.single C (.up ℤ) 0).obj M))) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M) := by
  rw [← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  apply (cancel_mono (U.mapDerivedCategoryFactors.hom.app
    ((HomologicalComplex.single D (.up ℤ) 0).obj (F.obj M)))).1
  simp only [Category.assoc]
  erw [Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]
  have hn := U.mapDerivedCategoryFactors.hom.naturality
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M)
  dsimp only [Functor.comp_map] at hn
  erw [hn, Iso.inv_hom_id_app_assoc]
  change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ =
    DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  congr 1
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases hi : i = 0
  · subst hi
    simp [Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq]
    change a.unit.app M ≫ (𝟙 _ ≫ U.map (𝟙 _)) = a.unit.app M ≫ U.map (𝟙 _)
    rw [Category.id_comp]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_src _ _

private theorem single_adjunct_formula (M : C) (P : D) (f : M ⟶ U.obj P) :
    (ad.homEquiv _ _).symm
      (DerivedCategory.Q.map
        ((a.mapHomologicalComplex (.up ℤ)).unit.app
          ((HomologicalComplex.single C (.up ℤ) 0).obj M)) ≫
        U.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj
          ((HomologicalComplex.single C (.up ℤ) 0).obj M))) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M ≫
          (HomologicalComplex.single D (.up ℤ) 0).map ((a.homEquiv _ _).symm f)) =
    adjointInsertion U ad f := by
  rw [Functor.map_comp, ← Category.assoc, ← single_unit_formula F U a E ad M]
  unfold adjointInsertion
  change (ad.homEquiv _ _).symm _ ≫
    (DerivedCategory.singleFunctor D 0).map ((a.homEquiv _ _).symm f) = _
  rw [← ad.homEquiv_naturality_right_symm]
  congr 1
  have hn := (U.mapDerivedCategorySingleFunctor 0).inv.naturality
    ((a.homEquiv _ _).symm f)
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp]
  have h : a.unit.app M ≫ U.map ((a.homEquiv _ _).symm f) = f :=
    (a.homEquiv _ _).apply_symm_apply f
  rw [h]

end Single

section Cochain
variable {C : Type v} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C]
  {D : Type w} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [SymmetricCategory D] [MonoidalClosed D]
  (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]

/- Local copies of the two private computation lemmas of
`Sheaf.AlgebraicGeometry.EtaleSingleCochainMonoidal` (not visible from this module). -/
private lemma singleCochainTensorIso_inv_f' (L M : C) :
    (AlgebraicGeometry.Etale.singleCochainTensorIso L M).inv.f 0 =
      HomologicalComplex.ιTensorObj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj L)
        ((HomologicalComplex.single _ (.up ℤ) 0).obj M) 0 0 0 rfl := by
  simp [AlgebraicGeometry.Etale.singleCochainTensorIso,
    CochainComplex.mapBifunctorSingle₁Iso_inv_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    HomologicalComplex.single, whiskerLeft_id]

private lemma singleCochainTensorIso_naturality'
    {L L' M M' : C} (f : L ⟶ L') (g : M ⟶ M') :
    ((HomologicalComplex.single _ (.up ℤ) 0).map f ⊗ₘ
        (HomologicalComplex.single _ (.up ℤ) 0).map g) ≫
      (AlgebraicGeometry.Etale.singleCochainTensorIso L' M').hom =
    (AlgebraicGeometry.Etale.singleCochainTensorIso L M).hom ≫
      (HomologicalComplex.single _ (.up ℤ) 0).map (f ⊗ₘ g) := by
  apply (cancel_epi (AlgebraicGeometry.Etale.singleCochainTensorIso L M).inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply (cancel_mono (AlgebraicGeometry.Etale.singleCochainTensorIso L' M').inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, singleCochainTensorIso_inv_f']
  simp only [tensorHom_def, HomologicalComplex.comp_f]
  erw [CochainComplex.Monoidal.ι_whiskerRight_assoc,
    CochainComplex.ιTensorObj_whiskerLeft_f]
  simp [HomologicalComplex.single, Category.assoc]

set_option linter.flexible false in
open AlgebraicGeometry.Etale in
private theorem single_tensor_map (M N : C) :
    ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app
        ((HomologicalComplex.single C (.up ℤ) 0).obj M)).app
        ((HomologicalComplex.single C (.up ℤ) 0).obj N) ≫
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M ⊗ₘ
        (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app N) ≫
      (singleCochainTensorIso (F.obj M) (F.obj N)).hom =
    (F.mapHomologicalComplex (.up ℤ)).map (singleCochainTensorIso M N).hom ≫
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app (M ⊗ N) ≫
      (HomologicalComplex.single D (.up ℤ) 0).map (Functor.OplaxMonoidal.δ F M N) := by
  apply (cancel_epi
    ((F.mapHomologicalComplex (.up ℤ)).mapIso (singleCochainTensorIso M N)).inv).1
  simp only [Functor.mapIso_inv, ← Functor.map_comp_assoc, Iso.inv_hom_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  apply (cancel_epi
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app (M ⊗ N))).1
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    singleCochainTensorIso_inv_f', Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app,
    HomologicalComplex.mapBifunctorComparison_f]
  erw [HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
  simp only [HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    HomologicalComplex.single, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp]
  simp only [tensorHom_def, HomologicalComplex.comp_f, Category.assoc]
  erw [CochainComplex.Monoidal.ι_whiskerRight_assoc,
    CochainComplex.ιTensorObj_whiskerLeft_f_assoc]
  simp [HomologicalComplex.mapBifunctorComparisonApp, Functor.OplaxMonoidal.δNatTrans,
    HomologicalComplex.single,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  have hs := congrArg (fun f ↦ f.f (0 : ℤ))
    (singleCochainTensorIso (F.obj M) (F.obj N)).inv_hom_id
  simp only [HomologicalComplex.comp_f, singleCochainTensorIso_inv_f',
    HomologicalComplex.id_f] at hs
  change HomologicalComplex.ιTensorObj
      ((HomologicalComplex.single D (.up ℤ) 0).obj (F.obj M))
      ((HomologicalComplex.single D (.up ℤ) 0).obj (F.obj N)) 0 0 0 rfl ≫
      (singleCochainTensorIso (F.obj M) (F.obj N)).hom.f 0 =
    𝟙 (F.obj M ⊗ F.obj N) at hs
  exact (congrArg (fun t : F.obj M ⊗ F.obj N ⟶ F.obj M ⊗ F.obj N ↦
    Functor.OplaxMonoidal.δ F M N ≫ t) hs).trans (Category.comp_id _)

end Cochain

section Normalized
variable {C : Type v} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory.{u + 1} C]
  {D : Type w} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
  [HasDerivedCategory.{u + 1} D]
  (F : C ⥤ D) (U : D ⥤ C) [F.Additive] [U.Additive]
  [F.OplaxMonoidal] [U.LaxMonoidal] [F.IsLeftAdjoint]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (a : F ⊣ U) [a.IsMonoidal]
  (E : DerivedCategory C ⥤ DerivedCategory D) (ad : E ⊣ U.mapDerivedCategory)

private def cochainRepresentative : DerivedCategory.Q ⋙ E ⟶
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := by
  let t := Functor.whiskerRight (a.mapHomologicalComplex (.up ℤ)).unit
      DerivedCategory.Q ≫
    Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ)) U.mapDerivedCategoryFactors.inv
  exact {
    app P := (ad.homEquiv _ _).symm (t.app P)
    naturality P Q f := by
      change E.map (DerivedCategory.Q.map f) ≫ _ = _ ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f)
      calc
        _ = (ad.homEquiv _ _).symm (DerivedCategory.Q.map f ≫ t.app Q) :=
          (ad.homEquiv_naturality_left_symm _ _).symm
        _ = (ad.homEquiv _ _).symm
            (t.app P ≫ U.mapDerivedCategory.map
              (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f))) :=
          congrArg (ad.homEquiv _ _).symm (t.naturality f)
        _ = _ := ad.homEquiv_naturality_right_symm _ _ }

open AlgebraicGeometry.Etale in
/-- The tensor of exact-single adjunction transposes is the transpose of the ordinary
lax tensor product, for any derived tensor comparison normalized on representatives.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-setup/sec-the-purity-statement/sk-thm-purity-transport/sk-thm-purity-transport.proof.md,
Step 1 (compatibility with the finite reductions), the finite scalar/tensor calculation.
(blueprint: lem-pur-normalized-tensor-adjunction-insertion)

Proof: factor each transpose through the localized ordinary adjunction unit.
Apply the representative tensor square to the two single complexes. Naturality
of localization's lax tensorator reduces the result to the ordinary tensor of
the two adjuncts. On the unique degree-zero summand the complex comparison is
the ordinary oplax tensorator. The monoidal adjunction identity identifies its
composite with the adjunct of the lax tensor of the original maps. Naturality
of the representative finishes the comparison. -/
theorem normalizedTensor_adjointInsertion
    (rep : ∀ P : CochainComplex C ℤ,
      E.obj (DerivedCategory.Q.obj P) ⟶
        DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (hrep : ∀ P : CochainComplex C ℤ, rep P = (ad.homEquiv _ _).symm
      (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        U.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P)))
    (δ : Functor.uncurry.obj (curriedTensor (DerivedCategory C)) ⋙ E ≅
      E.prod E ⋙ Functor.uncurry.obj (curriedTensor (DerivedCategory D)))
    (ht : ∀ P Q : CochainComplex C ℤ,
      δ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          (rep P ⊗ₘ
            rep Q) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q
            ((F.mapHomologicalComplex (.up ℤ)).obj P)
            ((F.mapHomologicalComplex (.up ℤ)).obj Q) =
        E.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
          rep (P ⊗ Q) ≫
          DerivedCategory.Q.map
            (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q))
    (M N : C) (P Q : D) (f : M ⟶ U.obj P) (g : N ⟶ U.obj Q) :
    δ.hom.app ((DerivedCategory.singleFunctor C 0).obj M,
        (DerivedCategory.singleFunctor C 0).obj N) ≫
        (adjointInsertion U ad f ⊗ₘ adjointInsertion U ad g) ≫
        (Functor.LaxMonoidal.μ DerivedCategory.Q
          ((HomologicalComplex.single D (.up ℤ) 0).obj P)
          ((HomologicalComplex.single D (.up ℤ) 0).obj Q) ≫
          DerivedCategory.Q.map (singleCochainTensorIso P Q).hom) =
      E.map ((Functor.LaxMonoidal.μ DerivedCategory.Q
          ((HomologicalComplex.single C (.up ℤ) 0).obj M)
          ((HomologicalComplex.single C (.up ℤ) 0).obj N) ≫
          DerivedCategory.Q.map (singleCochainTensorIso M N).hom)) ≫
        adjointInsertion U ad ((f ⊗ₘ g) ≫ Functor.LaxMonoidal.μ U P Q) := by
  let sc := HomologicalComplex.single C (.up ℤ) 0
  let sd := HomologicalComplex.single D (.up ℤ) 0
  let fc := F.mapHomologicalComplex (.up ℤ)
  let r := cochainRepresentative F U a E ad
  have hr (P : CochainComplex C ℤ) : rep P = r.app P := hrep P
  simp only [hr] at ht
  let k (M : C) (P : D) (f : M ⟶ U.obj P) : fc.obj (sc.obj M) ⟶ sd.obj P :=
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M ≫
      sd.map ((a.homEquiv _ _).symm f)
  have hi (M : C) (P : D) (f : M ⟶ U.obj P) :
      adjointInsertion U ad f = r.app (sc.obj M) ≫ DerivedCategory.Q.map (k M P f) :=
    (single_adjunct_formula F U a E ad M P f).symm
  have hk :
      ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app
        (sc.obj M)).app (sc.obj N) ≫
        (k M P f ⊗ₘ k N Q g) ≫ (singleCochainTensorIso P Q).hom =
      fc.map (singleCochainTensorIso M N).hom ≫
        k (M ⊗ N) (P ⊗ Q) ((f ⊗ₘ g) ≫ Functor.LaxMonoidal.μ U P Q) := by
    dsimp only [k]
    rw [← tensorHom_comp_tensorHom_assoc,
      singleCochainTensorIso_naturality',
      reassoc_of% single_tensor_map F M N,
      ← sd.map_comp, tensor_adjunct a f g]
  rw [hi M P f, hi N Q g,
    hi (M ⊗ N) (P ⊗ Q) ((f ⊗ₘ g) ≫ Functor.LaxMonoidal.μ U P Q)]
  change δ.hom.app (DerivedCategory.Q.obj (sc.obj M),
      DerivedCategory.Q.obj (sc.obj N)) ≫
      ((r.app (sc.obj M) ≫ DerivedCategory.Q.map (k M P f)) ⊗ₘ
        (r.app (sc.obj N) ≫ DerivedCategory.Q.map (k N Q g))) ≫
      (Functor.LaxMonoidal.μ DerivedCategory.Q (sd.obj P) (sd.obj Q) ≫
        DerivedCategory.Q.map (singleCochainTensorIso P Q).hom) =
    E.map (Functor.LaxMonoidal.μ DerivedCategory.Q (sc.obj M) (sc.obj N) ≫
      DerivedCategory.Q.map (singleCochainTensorIso M N).hom) ≫
      (r.app (sc.obj (M ⊗ N)) ≫ DerivedCategory.Q.map
        (k (M ⊗ N) (P ⊗ Q) ((f ⊗ₘ g) ≫ Functor.LaxMonoidal.μ U P Q)))
  rw [← tensorHom_comp_tensorHom_assoc]
  rw [Functor.LaxMonoidal.μ_natural_assoc, reassoc_of% ht]
  rw [← DerivedCategory.Q.map_comp_assoc, ← DerivedCategory.Q.map_comp, Category.assoc, hk,
    Functor.map_comp]
  have hn : E.map (DerivedCategory.Q.map (singleCochainTensorIso M N).hom) ≫
        r.app (sc.obj (M ⊗ N)) =
      r.app (sc.obj M ⊗ sc.obj N) ≫
        DerivedCategory.Q.map (fc.map (singleCochainTensorIso M N).hom) :=
    r.naturality (singleCochainTensorIso M N).hom
  rw [E.map_comp, Category.assoc, reassoc_of% hn]

end Normalized
end SheafExactDegreeZero
