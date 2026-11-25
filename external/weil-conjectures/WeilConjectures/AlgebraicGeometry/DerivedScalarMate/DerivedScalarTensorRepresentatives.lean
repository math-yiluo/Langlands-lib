/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarTensorOrdinary
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedFixedCoefficientTensorComparison
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

/-! # Scalar tensor comparison on resolving representatives

Source: Stacks Tags 06YY, 07A4 and 07A6
(blueprint: lem-sfb-scalar-tensor-representative-normalization).
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

private def scalarCounit {W : Scheme.{u}}
    {A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : A ⟶ B) :
    DerivedCategory.Q ⋙ proEtaleRingDerivedExtension φ ⋙ (restriction φ).mapDerivedCategory ⟶
      (proEtaleRingExtension φ).mapHomologicalComplex (.up ℤ) ⋙
        (restriction φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app P := (restriction φ).mapDerivedCategory.map
      ((proEtaleRingDerivedExtensionCounit φ).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
    (restriction φ).mapDerivedCategoryFactorsh.hom.app
      (((proEtaleRingExtension φ).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
  naturality := by
    intro P P' v
    have h := (proEtaleRingDerivedExtensionCounit φ).naturality
      ((HomotopyCategory.quotient _ (.up ℤ)).map v)
    have h' := (restriction φ).mapDerivedCategoryFactorsh.hom.naturality
      (((proEtaleRingExtension φ).mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient _ (.up ℤ)).map v))
    dsimp only [Functor.comp_map]
    dsimp only [Functor.comp_map] at h h'
    erw [← Functor.map_comp_assoc, h, Functor.map_comp, Category.assoc, h']
    rw [Category.assoc]
    rfl

private theorem scalarCounit_isIso {W : Scheme.{u}}
    {A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : A ⟶ B)
    (P : CochainComplex (proEtaleRingModules W A) ℤ)
    (hp : proEtaleFlatRepresentatives W A P) : IsIso ((scalarCounit φ).app P) := by
  have : IsIso ((proEtaleRingDerivedExtensionCounit φ).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
    (reductionDerivedExistence W φ).choose_spec.choose_spec.2.2 P
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hp.1)
  dsimp only [scalarCounit]
  infer_instance

private theorem ordinaryComplexIso_naturality {W : Scheme.{u}}
    {A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : A ⟶ B)
    {P P' : CochainComplex (proEtaleRingModules W A) ℤ} (v : P ⟶ P') :
    ((restriction φ).mapHomologicalComplex (.up ℤ)).map
        (((proEtaleRingExtension φ).mapHomologicalComplex (.up ℤ)).map v) ≫
      (ordinaryComplexIso φ P').hom =
    (ordinaryComplexIso φ P).hom ≫
      HomologicalComplex.mapBifunctorMap v (𝟙 (coefficientComplex φ))
        (proEtaleOrdinaryTensor W A) (.up ℤ) := by
  let c := Functor.mapHomologicalComplexCompIso (ordinaryTensorIso φ) (.up ℤ)
  have hc := c.hom.naturality v
  have hs := CochainComplex.mapBifunctorSingle₂Iso_inv_naturality
    (proEtaleOrdinaryTensor W A) (coefficient φ) v
  dsimp only [ordinaryComplexIso, Iso.trans_hom, Iso.symm_hom]
  dsimp only [Functor.comp_map] at hc
  erw [← Category.assoc, hc, Category.assoc, ← hs]
  rw [Category.assoc]
  rfl

attribute [local irreducible] ordinaryComplexIso

/-- The scalar/tensor comparison on flat-term K-flat representatives.
Source: Stacks 06YY, 07A4, 07A6
(blueprint: lem-sfb-scalar-tensor-representative-normalization).
Proof: resolve the coefficient complex by a flat-term K-flat Q. Tensoring its
augmentation with a K-flat P is a quasi-isomorphism. Compose the inverse of this
map with the tensor-model representative and the localized augmentation. The
fixed-factor comparison identifies this composite for every other augmentation.
Compose with the invertible scalar counit and ordinary complex comparison. Their
naturality makes this an isomorphism of functors on the representative category.
Cancel the component isomorphisms to obtain the stated normalization. -/
theorem representativeScalarTensorIso
    {W : Scheme.{u}}
    {A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) (a : ProEtaleTensorModel W A) :
    ∃ b : ((proEtaleFlatRepresentatives W A).ι ⋙ DerivedCategory.Q) ⋙
          proEtaleRingDerivedExtension φ ⋙ (restriction φ).mapDerivedCategory ≅
        ((proEtaleFlatRepresentatives W A).ι ⋙ DerivedCategory.Q) ⋙
          (Functor.curryObj a.tensor).flip.obj
            (DerivedCategory.Q.obj (coefficientComplex φ)),
      ∀ (P Q : CochainComplex (proEtaleRingModules W A) ℤ)
        (hp : proEtaleFlatRepresentatives W A P)
        (hq : proEtaleFlatRepresentatives W A Q)
        (q : Q ⟶ coefficientComplex φ), QuasiIso q →
        a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) ≫
          a.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map q)) ≫
          b.inv.app ⟨P, hp⟩ ≫
          (restriction φ).mapDerivedCategory.map
            (cast (by rfl) ((proEtaleRingDerivedExtensionCounit φ).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) ≫
          (restriction φ).mapDerivedCategoryFactorsh.hom.app
            (((proEtaleRingExtension φ).mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
        cast (by rfl) (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 P) q
          (proEtaleOrdinaryTensor W A) (.up ℤ) ≫ (ordinaryComplexIso φ P).inv)) := by
  classical
  let M := proEtaleRingModules W A
  let PR := proEtaleFlatRepresentatives W A
  let L := PR.ι ⋙ (DerivedCategory.Q : CochainComplex M ℤ ⥤ DerivedCategory M)
  let T := (proEtaleOrdinaryTensor W A).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)
  let F := proEtaleRingDerivedExtension φ ⋙ (restriction φ).mapDerivedCategory
  let G := (Functor.curryObj a.tensor).flip.obj (DerivedCategory.Q.obj (coefficientComplex φ))
  obtain ⟨e, he⟩ := fixedCoefficientTensorIso φ a
  let k := Functor.whiskerLeft PR.ι (scalarCounit φ)
  have (P : PR.FullSubcategory) : IsIso (k.app P) :=
    scalarCounit_isIso φ P.obj P.property
  have : IsIso k := NatIso.isIso_of_isIso_app k
  let c : PR.ι ⋙ (proEtaleRingExtension φ).mapHomologicalComplex (.up ℤ) ⋙
        (restriction φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅
      PR.ι ⋙ T.flip.obj (coefficientComplex φ) ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun P ↦ DerivedCategory.Q.mapIso (ordinaryComplexIso φ P.obj)) (by
      intro P P' v
      dsimp only [Functor.comp_map, Functor.mapIso_hom]
      erw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg DerivedCategory.Q.map (ordinaryComplexIso_naturality φ v.hom))
  let b : L ⋙ F ≅ L ⋙ G := asIso k ≪≫ c ≪≫ e
  refine ⟨b, ?_⟩
  intro P H hp hH v _hv
  change a.representative.hom.app (⟨P, hp⟩, ⟨H, hH⟩) ≫
    a.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map v)) ≫
    b.inv.app ⟨P, hp⟩ ≫ (scalarCounit φ).app P = _
  erw [reassoc_of% (he ⟨P, hp⟩ H hH v)]
  dsimp only [b, Iso.trans_inv, NatTrans.comp_app, asIso_inv]
  simp only [NatIso.isIso_inv_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  change DerivedCategory.Q.map
    (HomologicalComplex.mapBifunctorMap (𝟙 P) v (proEtaleOrdinaryTensor W A) (.up ℤ)) ≫
    c.inv.app ⟨P, hp⟩ ≫ inv (k.app ⟨P, hp⟩) ≫ k.app ⟨P, hp⟩ = _
  simp only [IsIso.inv_hom_id, Category.comp_id]
  dsimp only [c, NatIso.ofComponents_inv_app, Functor.mapIso_inv]
  change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ = DerivedCategory.Q.map _
  rw [← Functor.map_comp]

end AlgebraicGeometry.Scheme.DerivedScalarMate
