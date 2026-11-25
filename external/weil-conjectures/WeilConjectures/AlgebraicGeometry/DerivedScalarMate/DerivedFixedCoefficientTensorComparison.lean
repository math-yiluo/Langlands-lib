/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarTensorOrdinary
import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedTensorRepresentativeComparison
import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Fixed-coefficient tensor normalization on representatives

Source: Stacks Tags 06YY, 07A4 and 07A6
(blueprint: lem-sfb-fixed-coefficient-tensor-representative-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme.DerivedScalarMate
attribute [local irreducible] SheafOfModules.monoidalCategory ordinaryTensorIso
  CategoryTheory.Functor.leftAdjoint CategoryTheory.presheafToSheaf HomologicalComplex₂.total
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex

private theorem coefficientResolution {W : Scheme.{u}}
    {A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : A ⟶ B) :
    ∃ (Q : CochainComplex (proEtaleRingModules W A) ℤ)
      (_hq : proEtaleFlatRepresentatives W A Q) (q : Q ⟶ coefficientComplex φ), QuasiIso q := by
  obtain ⟨Q, q, hk, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := A)
      (coefficientComplex φ)
  exact ⟨Q, ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Q).1 hk,
    fun n ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso A (Q.X n)).symm (hf n)⟩, q, hq⟩

private theorem tensorResolution_isIso {W : Scheme.{u}}
    {A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : A ⟶ B)
    (P : CochainComplex (proEtaleRingModules W A) ℤ)
    (hp : proEtaleFlatRepresentatives W A P)
    {Q : CochainComplex (proEtaleRingModules W A) ℤ}
    (q : Q ⟶ coefficientComplex φ) (hq : QuasiIso q) :
    IsIso (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 P) q
      (proEtaleOrdinaryTensor W A) (.up ℤ))) := by
  obtain ⟨_, ht⟩ := SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated A
  have hk := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hp.1
  have hh := (ht P hk hp.2).1 Q (coefficientComplex φ) q hq |>.1
  let T := (proEtaleOrdinaryTensor W A).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)
  have he : HomologicalComplex.mapBifunctorMap (𝟙 P) q
      (proEtaleOrdinaryTensor W A) (.up ℤ) = (T.obj P).map q := rfl
  rw [he]
  have : QuasiIso ((T.obj P).map q) := hh
  infer_instance

private theorem fixedCoefficientComparison {W : Scheme.{u}}
    {A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : A ⟶ B)
    (a : ProEtaleTensorModel W A)
    (P : CochainComplex (proEtaleRingModules W A) ℤ)
    (hp : proEtaleFlatRepresentatives W A P) :
    ∃ d : DerivedCategory.Q.obj
        (CochainComplex.mapBifunctor P (coefficientComplex φ) (proEtaleOrdinaryTensor W A)) ≅
        a.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj (coefficientComplex φ)),
      ∀ (Q : CochainComplex (proEtaleRingModules W A) ℤ)
        (hq : proEtaleFlatRepresentatives W A Q) (q : Q ⟶ coefficientComplex φ),
        a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) ≫
          a.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map q)) =
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 P) q
          (proEtaleOrdinaryTensor W A) (.up ℤ)) ≫ d.hom := by
  obtain ⟨d, hd⟩ := proEtale_fixed_tensor_representative_comparison W A a P hp
  refine ⟨d.app (coefficientComplex φ), ?_⟩
  intro Q hq q
  have hn := d.hom.naturality q
  dsimp only [Functor.comp_map, Functor.prod'_map, Functor.const_obj_map, Functor.id_map,
    Functor.prod'_obj, Functor.const_obj_obj, Functor.id_obj, Functor.uncurry_obj_map] at hn
  erw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at hn
  change DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 P) q
      (proEtaleOrdinaryTensor W A) (.up ℤ)) ≫ d.hom.app (coefficientComplex φ) =
    d.hom.app Q ≫ a.tensor.map
      (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map q)) at hn
  rw [hd Q hq] at hn
  exact hn.symm

private noncomputable def representativeFixedIso
    (W : Scheme.{u}) (A : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (a : ProEtaleTensorModel W A)
    (Q : CochainComplex (proEtaleRingModules W A) ℤ)
    (hQ : proEtaleFlatRepresentatives W A Q) :
    (proEtaleFlatRepresentatives W A).ι ⋙
        ((proEtaleOrdinaryTensor W A).map₂HomologicalComplex
          (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj Q ⋙ DerivedCategory.Q ≅
      ((proEtaleFlatRepresentatives W A).ι ⋙ DerivedCategory.Q) ⋙
        (Functor.curryObj a.tensor).flip.obj (DerivedCategory.Q.obj Q) :=
  NatIso.ofComponents (fun P ↦ a.representative.app (P, ⟨Q, hQ⟩)) (by
    intro P P' v
    have hn := a.representative.hom.naturality
      (X := (P, ⟨Q, hQ⟩)) (Y := (P', ⟨Q, hQ⟩))
      (Prod.mkHom v (𝟙 (⟨Q, hQ⟩ : (proEtaleFlatRepresentatives W A).FullSubcategory)))
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj, Functor.comp_obj,
      Functor.uncurry_obj_obj, Functor.uncurry_obj_map, ObjectProperty.ι_obj,
      ObjectProperty.ι_map, ObjectProperty.FullSubcategory.id_hom] at hn
    simp only [CategoryTheory.Functor.map_id, Category.comp_id] at hn
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.flip,
      Functor.curryObj, ObjectProperty.ι_obj, ObjectProperty.ι_map]
    simpa only [Iso.app_hom] using hn)

private theorem representativeFixedIso_hom_app
    (W : Scheme.{u}) (A : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (a : ProEtaleTensorModel W A)
    (Q : CochainComplex (proEtaleRingModules W A) ℤ)
    (hQ : proEtaleFlatRepresentatives W A Q)
    (P : (proEtaleFlatRepresentatives W A).FullSubcategory) :
    (representativeFixedIso W A a Q hQ).hom.app P =
      a.representative.hom.app (P, ⟨Q, hQ⟩) := by
  simp only [representativeFixedIso, NatIso.ofComponents_hom_app, Iso.app_hom]

attribute [local irreducible] representativeFixedIso

/-- A fixed coefficient computes derived tensor on every flat K-flat first factor.
Source: Stacks 07A4
(blueprint: lem-sfb-fixed-coefficient-tensor-representative-normalization).
Proof: choose a flat-term K-flat resolution q of the coefficient complex.
Tensoring q with a K-flat first factor gives a quasi-isomorphism. Invert its
localized map and compose with the model representative and tensor(1,Qq).
The fixed-factor representative comparison identifies the resulting component
with its canonical component at the coefficient complex. Naturality of that
comparison proves the same formula for every map from any other flat K-flat H.
Naturality in the first factor follows by composing natural isomorphisms. -/
theorem fixedCoefficientTensorIso
    {W : Scheme.{u}}
    {A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) (a : ProEtaleTensorModel W A) :
    ∃ e : (proEtaleFlatRepresentatives W A).ι ⋙
          ((proEtaleOrdinaryTensor W A).map₂HomologicalComplex
            (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj (coefficientComplex φ) ⋙ DerivedCategory.Q ≅
        ((proEtaleFlatRepresentatives W A).ι ⋙ DerivedCategory.Q) ⋙
          (Functor.curryObj a.tensor).flip.obj
            (DerivedCategory.Q.obj (coefficientComplex φ)),
      ∀ (P : (proEtaleFlatRepresentatives W A).FullSubcategory)
        (H : CochainComplex (proEtaleRingModules W A) ℤ)
        (hH : proEtaleFlatRepresentatives W A H) (v : H ⟶ coefficientComplex φ),
        a.representative.hom.app (P, ⟨H, hH⟩) ≫
          a.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P.obj))
            (DerivedCategory.Q.map v)) =
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 P.obj) v
          (proEtaleOrdinaryTensor W A) (.up ℤ)) ≫ e.hom.app P := by
  classical
  let M := proEtaleRingModules W A
  let PR := proEtaleFlatRepresentatives W A
  let L := PR.ι ⋙ (DerivedCategory.Q : CochainComplex M ℤ ⥤ DerivedCategory M)
  let T := (proEtaleOrdinaryTensor W A).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)
  let G := (Functor.curryObj a.tensor).flip.obj (DerivedCategory.Q.obj (coefficientComplex φ))
  obtain ⟨Q, hQ, q, hq⟩ := coefficientResolution φ
  have : QuasiIso q := hq
  let s : PR.ι ⋙ T.flip.obj Q ⋙ DerivedCategory.Q ⟶
      PR.ι ⋙ T.flip.obj (coefficientComplex φ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (Functor.whiskerLeft PR.ι (T.flip.map q)) DerivedCategory.Q
  have hs (P : PR.FullSubcategory) : s.app P =
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 P.obj) q
        (proEtaleOrdinaryTensor W A) (.up ℤ)) := by
    dsimp only [s, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    rfl
  have (P : PR.FullSubcategory) : IsIso (s.app P) := by
    rw [hs]
    exact tensorResolution_isIso φ P.obj P.property q hq
  have : IsIso s := NatIso.isIso_of_isIso_app s
  let r := representativeFixedIso W A a Q hQ
  let t := Functor.isoWhiskerLeft L
    ((Functor.curryObj a.tensor).flip.mapIso (asIso (DerivedCategory.Q.map q)))
  let e : PR.ι ⋙ T.flip.obj (coefficientComplex φ) ⋙ DerivedCategory.Q ≅ L ⋙ G :=
    (asIso s).symm ≪≫ r ≪≫ t
  have he (P : PR.FullSubcategory)
      (H : CochainComplex M ℤ) (hH : PR H) (v : H ⟶ coefficientComplex φ) :
      a.representative.hom.app (P, ⟨H, hH⟩) ≫
        a.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P.obj)) (DerivedCategory.Q.map v)) =
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 P.obj) v
        (proEtaleOrdinaryTensor W A) (.up ℤ)) ≫ e.hom.app P := by
    obtain ⟨d, hd⟩ := fixedCoefficientComparison φ a P.obj P.property
    have hed : e.hom.app P = d.hom := by
      apply (cancel_epi (s.app P)).mp
      dsimp only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, asIso_inv]
      simp only [NatIso.isIso_inv_app, IsIso.hom_inv_id_assoc]
      rw [hs, representativeFixedIso_hom_app]
      exact hd Q hQ q
    rw [hed]
    exact hd H hH v
  exact ⟨e, he⟩

end AlgebraicGeometry.Scheme.DerivedScalarMate
