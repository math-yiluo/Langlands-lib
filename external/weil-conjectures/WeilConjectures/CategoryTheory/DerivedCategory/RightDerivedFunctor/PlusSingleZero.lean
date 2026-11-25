/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.Mathlib.CategoryTheory.Comma.Arrow

/-!
# The degree-zero part of a right derived functor on a single object

For a left exact functor `F` between abelian categories, the unit
`F(X[0]) ⟶ R⁺F(X[0])` of the right derived functor on the bounded below derived categories is
an isomorphism on `H⁰`
(`CategoryTheory.Functor.isIso_homologyFunctor_zero_map_rightDerivedFunctorPlusUnit_app`): on
an injective resolution `X ⟶ I`, the map `F X ⟶ F(I)` is a quasi-isomorphism in degree `0` by
left exactness
(`CategoryTheory.InjectiveResolution.quasiIsoAt_mapHomologicalComplex_map_ι'_zero`).

We also record that `H⁰` of the map of single complexes induced by a natural transformation
`τ` at `X` is isomorphic, as an arrow, to `τ.app X`.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.InjectiveResolution

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] {X : C} (R : InjectiveResolution X)

/-- A left exact functor sends an injective resolution `X ⟶ I` to a map `F X ⟶ F(I)` which is a
quasi-isomorphism in degree `0`. -/
lemma quasiIsoAt_mapHomologicalComplex_map_ι_zero :
    QuasiIsoAt ((F.mapHomologicalComplex _).map R.ι) 0 := by
  rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
  · rw [ShortComplex.exact_and_mono_f_iff_f_is_kernel]
    exact ⟨KernelFork.mapIsLimit _ R.isLimitKernelFork F⟩
  all_goals simp

/-- The `ℤ`-indexed form: `F(X[0]) ⟶ F(I)` is a quasi-isomorphism in degree `0`. -/
lemma quasiIsoAt_mapHomologicalComplex_map_ι'_zero :
    QuasiIsoAt ((F.mapHomologicalComplex _).map R.ι') 0 := by
  have e1 : (F.mapHomologicalComplex _).map (HomologicalComplex.extendMap R.ι
      ComplexShape.embeddingUpNat) =
      (HomologicalComplex.mapExtendIso _ ComplexShape.embeddingUpNat F).hom ≫
        HomologicalComplex.extendMap ((F.mapHomologicalComplex _).map R.ι)
          ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.mapExtendIso _ ComplexShape.embeddingUpNat F).inv := by
    ext i
    simp only [Functor.mapHomologicalComplex_map_f, HomologicalComplex.comp_f,
      ← HomologicalComplex.mapExtensIso_hom_f_naturality_assoc]
    rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
    exact (Category.comp_id _).symm
  have h₀ : QuasiIsoAt (HomologicalComplex.extendMap ((F.mapHomologicalComplex _).map R.ι)
      ComplexShape.embeddingUpNat) 0 :=
    (HomologicalComplex.quasiIsoAt_extendMap_iff _ _ (j := 0) (hj' := rfl)).2
      (quasiIsoAt_mapHomologicalComplex_map_ι_zero F R)
  have h₁ : QuasiIsoAt ((F.mapHomologicalComplex _).map (HomologicalComplex.extendMap R.ι
      ComplexShape.embeddingUpNat)) 0 := by
    rw [e1]
    infer_instance
  rw [InjectiveResolution.ι', Functor.map_comp]
  exact (quasiIsoAt_iff_comp_left _ _ _).2 h₁

end CategoryTheory.InjectiveResolution

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- For a left exact functor `F`, `H⁰` of the unit `F(X[0]) ⟶ R⁺F(X[0])` is an isomorphism. -/
lemma isIso_homologyFunctor_zero_map_rightDerivedFunctorPlusUnit_app (X : C) :
    IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient C).obj
        ⟨(HomologicalComplex.single C (.up ℤ) 0).obj X, 0, inferInstance⟩))) := by
  let R := injectiveResolution X
  let L : CochainComplex.Plus C := ⟨R.cochainComplex, 0, inferInstance⟩
  have : ∀ n, Injective (L.obj.X n) := fun n ↦ inferInstanceAs (Injective (R.cochainComplex.X n))
  let f : (⟨(HomologicalComplex.single C (.up ℤ) 0).obj X, 0, inferInstance⟩ :
      CochainComplex.Plus C) ⟶ L := ObjectProperty.homMk R.ι'
  have hn := F.rightDerivedFunctorPlusUnith.naturality ((HomotopyCategory.Plus.quotient C).map f)
  have hL : IsIso (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj L)) :=
    inferInstance
  have hq : IsIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map f)) :=
    Localization.inverts _ (HomotopyCategory.Plus.quasiIso C) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff R.ι').2
        (by rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance))
  have hF : IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map (DerivedCategory.Plus.Q.map
      ((F.mapCochainComplexPlus).map f))) := by
    have := R.quasiIsoAt_mapHomologicalComplex_map_ι'_zero F
    have : IsIso (HomologicalComplex.homologyMap (F.mapCochainComplexPlus.map f).hom 0) := by
      change IsIso (HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map R.ι') 0)
      infer_instance
    have h := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality
      ((F.mapCochainComplexPlus).map f) 0
    rw [← Iso.eq_comp_inv] at h
    rw [h]
    infer_instance
  have hF' : IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map (DerivedCategory.Plus.Qh.map
      (F.mapHomotopyCategoryPlus.map ((HomotopyCategory.Plus.quotient C).map f)))) := by
    exact (NatIso.isIso_map_iff
      (isoWhiskerRight (DerivedCategory.Plus.quotientCompQhIso D)
        (DerivedCategory.Plus.homologyFunctor D 0)) (F.mapCochainComplexPlus.map f)).mpr hF
  have h := congrArg (DerivedCategory.Plus.homologyFunctor D 0).map hn
  simp only [Functor.comp_map, Functor.map_comp] at h
  rw [← IsIso.comp_inv_eq] at h
  erw [← h]
  infer_instance

end CategoryTheory.Functor

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

set_option linter.flexible false in
/-- `H⁰` of the map of single complexes induced by a natural transformation `τ` at `X` is
isomorphic, as an arrow, to `τ.app X`. -/
noncomputable def arrowIsoHomologyMapMapHomologicalComplexSingle (G G' : C ⥤ D) [G.Additive]
    [G'.Additive] (τ : G ⟶ G') (X : C) :
    Arrow.mk (HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app
      ((HomologicalComplex.single C (.up ℤ) 0).obj X)) 0) ≅ Arrow.mk (τ.app X) := by
  let e := (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).app X
  let e' := (HomologicalComplex.singleMapHomologicalComplex G' (.up ℤ) 0).app X
  have hw : (NatTrans.mapHomologicalComplex τ (.up ℤ)).app
      ((HomologicalComplex.single C (.up ℤ) 0).obj X) =
      e.hom ≫ (HomologicalComplex.single D (.up ℤ) 0).map (τ.app X) ≫ e'.inv := by
    ext i
    by_cases hi : i = 0
    · subst hi
      simp [e, e', HomologicalComplex.singleMapHomologicalComplex,
        HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf,
        HomologicalComplex.singleObjXIsoOfEq]
      erw [Category.comp_id]
      rfl
    · exact (G.map_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)).eq_of_src _ _
  refine Arrow.isoOfCompEq (𝟙 _)
    (HomologicalComplex.homologyMap e.hom 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (G.obj X)).hom)
    ((HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (G'.obj X)).inv ≫
      HomologicalComplex.homologyMap e'.inv 0) ?_
  rw [hw, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
    Category.id_comp]
  simp only [Category.assoc]
  congr 1
  rw [← HomologicalComplex.singleObjHomologySelfIso_hom_naturality_assoc, Iso.hom_inv_id_assoc]

end CategoryTheory
