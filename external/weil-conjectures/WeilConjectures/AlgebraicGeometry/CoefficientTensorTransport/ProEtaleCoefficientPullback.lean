/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackModels
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement

/-! # Normalization of exact derived coefficient pullback

(blueprint: lem-pbc-coefficient-pullback-factorization)
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
attribute [local instance]
  AlgebraicGeometry.Scheme.proEtaleRingRestrictionPullbackInv_isIso
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.pbcDerivedRestrict
  SheafOfModules.restrictScalars
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint
  AlgebraicGeometry.Scheme.proEtaleRingDerivedPullbackFactors SheafOfModules.monoidalCategory

private theorem complexComp_refl_hom
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (P : CochainComplex C ℤ) :
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app P =
      𝟙 _ := by
  ext n
  rfl

private theorem derivedId_factors
    (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]
    (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj P) =
      (𝟭 C).mapDerivedCategoryFactors.hom.app P := by
  rw [Functor.mapDerivedCategoryIdIso_hom_app]
  have h : (Functor.mapHomologicalComplexIdIso C (.up ℤ)).hom.app P = 𝟙 _ := rfl
  rw [h]
  erw [DerivedCategory.Q.map_id, Category.comp_id]

private theorem derivedRefl_factors
    (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]
    (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryNatIso (Iso.refl (𝟭 C)) ≪≫
      Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj P) =
      (𝟭 C).mapDerivedCategoryFactors.hom.app P := by
  have hn := Functor.mapDerivedCategoryNatIso_fac (Iso.refl (𝟭 C)) P
  change _ ≫ _ = _ ≫ DerivedCategory.Q.map (𝟙 _) at hn
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at hn
  dsimp only [Iso.trans_hom, NatTrans.comp_app]
  rw [derivedId_factors]
  exact hn

private theorem derivedComp_factors
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj P) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
        (F ⋙ G).mapDerivedCategoryFactors.hom.app P := by
  have h := Functor.mapDerivedCategoryCompIso_fac F G P
  erw [complexComp_refl_hom, CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

private theorem complex_left_id_hom
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (U : D ⥤ E) (G : C ⥤ E)
    [F.Additive] [U.Additive] [G.Additive] (e : F ⋙ U ≅ (𝟭 C) ⋙ G)
    (P : CochainComplex C ℤ) :
    (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P =
      (Functor.mapHomologicalComplexCompIso
        (e ≪≫ isoWhiskerRight (Iso.refl (𝟭 C)) G ≪≫ G.leftUnitor) (.up ℤ)).hom.app P := by
  apply HomologicalComplex.hom_ext
  intro n
  change e.hom.app (P.X n) = e.hom.app (P.X n) ≫ G.map (𝟙 _) ≫ 𝟙 _
  erw [G.map_id, Category.comp_id]
  exact (Category.comp_id (e.hom.app (P.X n))).symm

private theorem paste_pullback_factors
    {C : Type*} [Category C] {W X Y Z A B D : C}
    (a : X ≅ Y) (b : W ≅ X) (c : W ≅ Z)
    (m : Y ⟶ A) (i : A ⟶ B) (uv : Z ⟶ D) (v : X ⟶ B) (l : W ⟶ D) (e : D ⟶ B)
    (h₁ : a.hom ≫ m ≫ i = v) (h₂ : c.hom ≫ uv = l)
    (h₃ : b.hom ≫ v = l ≫ e) :
    c.inv ≫ b.hom ≫ a.hom ≫ m ≫ i = uv ≫ e := by
  rw [h₁, h₃, ← reassoc_of% h₂, Iso.inv_hom_id_assoc]

private theorem exactPullback_factors
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (L : C ⥤ D) (U : D ⥤ E) (M : C ⥤ E)
    [L.Additive] [U.Additive] [M.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits M] [PreservesFiniteColimits M]
    (e : L ⋙ U ≅ (𝟭 C) ⋙ M) (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryCompIso L U).hom.app (DerivedCategory.Q.obj P) ≫
      (Functor.mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Q.obj P) ≫
      (Functor.mapDerivedCategoryCompIso (𝟭 C) M).inv.app (DerivedCategory.Q.obj P) ≫
      M.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso (Iso.refl (𝟭 C)) ≪≫
          Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj P)) ≫
      M.mapDerivedCategoryFactors.hom.app P =
    U.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app P) ≫
      U.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso
          (e ≪≫ isoWhiskerRight (Iso.refl (𝟭 C)) M ≪≫ M.leftUnitor) (.up ℤ)).hom.app P) := by
  rw [derivedRefl_factors]
  have h₁ := derivedComp_factors (𝟭 C) M P
  have h₂ := derivedComp_factors L U P
  have h₃ := Functor.mapDerivedCategoryNatIso_fac e P
  have hn := paste_pullback_factors
    ((Functor.mapDerivedCategoryCompIso (𝟭 C) M).symm.app (DerivedCategory.Q.obj P))
    ((Functor.mapDerivedCategoryNatIso e).app (DerivedCategory.Q.obj P))
    ((Functor.mapDerivedCategoryCompIso L U).symm.app (DerivedCategory.Q.obj P))
    _ (M.mapDerivedCategoryFactors.hom.app P) _ _ _ _ h₁ h₂ h₃
  have ht := hn.trans (congrArg (fun t ↦
    (U.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app P) ≫
      U.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map t) (complex_left_id_hom L U M e P))
  simpa only [Category.assoc, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv] using ht

namespace AlgebraicGeometry.Scheme.CoefficientTensorChain

/-- Signed direct-sum total tensor on complexes, before localization. -/
abbrev total (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  Functor.uncurry.obj ((proEtaleOrdinaryTensor X R).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

/-- The canonical ordinary restriction/pullback comparison with base identity removed. -/
def ordinaryPullback :
    proEtaleRingModulePullback f R S c ⋙ pbcRestrict c.hom ≅
      proEtaleRingModulePullback f R
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _) :=
  (asIso (proEtaleRingRestrictionPullbackInv f R R
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) S
    (𝟙 R) c.hom (Iso.refl _) c (by simp))).symm ≪≫
    isoWhiskerRight (Iso.refl _) _ ≪≫ Functor.leftUnitor _

/-- Its termwise comparison on cochain complexes. -/
def complexPullback :
    (proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ) ⋙
        (pbcRestrict c.hom).mapHomologicalComplex (.up ℤ) ≅
      (proEtaleRingModulePullback f R
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
        (Iso.refl _)).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (ordinaryPullback f R S c) (.up ℤ)

end AlgebraicGeometry.Scheme.CoefficientTensorChain

namespace AlgebraicGeometry.Scheme.CoefficientTensorTransport

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

/-- Exact derived restriction along the identity, identified with the identity functor.
Source: functoriality of exact derived functors; Stacks Tag 07A6. -/
def identityRestriction : pbcDerivedRestrict (𝟙 R) ≅
    𝟭 (DerivedCategory (proEtaleRingModules Y R)) :=
  Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
    Functor.mapDerivedCategoryIdIso (proEtaleRingModules Y R)

/-- The canonical pullback comparison, with identity restriction on the base removed.
Source: Stacks Tags 0D6D and 07A6. -/
def pullback :
    proEtaleRingDerivedPullback f R S c ⋙ pbcDerivedRestrict c.hom ≅
      proEtaleRingDerivedPullback f R
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _) :=
  proEtaleRingRestrictionDerivedPullback f R R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) S
      (𝟙 R) c.hom (Iso.refl _) c (by simp) ≪≫
    isoWhiskerRight (identityRestriction R) _ ≪≫ Functor.leftUnitor _

end AlgebraicGeometry.Scheme.CoefficientTensorTransport

namespace AlgebraicGeometry.Scheme.CoefficientTensorTransport

attribute [local irreducible] CoefficientTensorChain.complexPullback pullback

/-- The canonical derived pullback comparison is the localization of the specified
ordinary comparison on every complex.

Source: exact derived functor identity, composition and natural-isomorphism
factorizations; Stacks Tag 07A6.
(blueprint: lem-pbc-coefficient-pullback-factorization)

Proof: the identity derived comparison agrees with the identity exact-functor
factorization. Apply mapDerivedCategoryCompIso_fac to both sides of the ordinary
restriction mate, and mapDerivedCategoryNatIso_fac to that mate. Cancel the two
composition comparisons. Removing the identity restriction leaves precisely the
termwise ordinary comparison complexPullback. -/
theorem pullback_factors {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (P : CochainComplex (proEtaleRingModules Y R) ℤ) :
    (pullback f R S c).hom.app (DerivedCategory.Q.obj P) ≫
        (proEtaleRingDerivedPullbackFactors f R
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
          (Iso.refl _)).hom.app P =
      (pbcDerivedRestrict c.hom).map
          ((proEtaleRingDerivedPullbackFactors f R S c).hom.app P) ≫
        (pbcRestrict c.hom).mapDerivedCategoryFactors.hom.app
          (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((CoefficientTensorChain.complexPullback f R S c).hom.app P) := by
  let L := proEtaleRingModulePullback f R S c
  let M := proEtaleRingModulePullback f R
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _)
  let U := pbcRestrict c.hom
  let e : L ⋙ U ≅ (𝟭 (proEtaleRingModules Y R)) ⋙ M :=
    (asIso (proEtaleRingRestrictionPullbackInv f R R
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) S
    (𝟙 R) c.hom (Iso.refl _) c (by simp))).symm
  unfold pullback proEtaleRingDerivedPullbackFactors
    proEtaleRingRestrictionDerivedPullback identityRestriction
    CoefficientTensorChain.complexPullback CoefficientTensorChain.ordinaryPullback
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    whiskerRight_app, leftUnitor_hom_app, Category.assoc]
  erw [Category.id_comp]
  change (Functor.mapDerivedCategoryCompIso L U).hom.app (DerivedCategory.Q.obj P) ≫
      (Functor.mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Q.obj P) ≫
      (Functor.mapDerivedCategoryCompIso (𝟭 (proEtaleRingModules Y R)) M).inv.app
        (DerivedCategory.Q.obj P) ≫
      M.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso (Iso.refl (𝟭 (proEtaleRingModules Y R))) ≪≫
          Functor.mapDerivedCategoryIdIso (proEtaleRingModules Y R)).hom.app
            (DerivedCategory.Q.obj P)) ≫
      M.mapDerivedCategoryFactors.hom.app P =
    U.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app P) ≫
      U.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso
          (e ≪≫ isoWhiskerRight (Iso.refl (𝟭 (proEtaleRingModules Y R))) M ≪≫
            M.leftUnitor) (.up ℤ)).hom.app P)
  exact exactPullback_factors L U M e P

/-- Product of the two canonical coefficient pullback factorization squares.
Source: exact-derived factorization, Stacks Tag 07A6.
(blueprint: lem-pbc-coefficient-pullback-factorization) -/
theorem pullback_pair_factors {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (P Q : CochainComplex (proEtaleRingModules Y R) ℤ) :
    Prod.mkHom ((pullback f R S c).hom.app (DerivedCategory.Q.obj P))
      ((pullback f R S c).hom.app (DerivedCategory.Q.obj Q)) ≫
      Prod.mkHom ((proEtaleRingDerivedPullbackFactors f R
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _)).hom.app P)
        ((proEtaleRingDerivedPullbackFactors f R
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _)).hom.app Q) =
    ((pbcDerivedRestrict c.hom).prod (pbcDerivedRestrict c.hom)).map
      (Prod.mkHom ((proEtaleRingDerivedPullbackFactors f R S c).hom.app P)
        ((proEtaleRingDerivedPullbackFactors f R S c).hom.app Q)) ≫
      Prod.mkHom ((pbcRestrict c.hom).mapDerivedCategoryFactors.hom.app
        (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P))
        ((pbcRestrict c.hom).mapDerivedCategoryFactors.hom.app
          (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj Q)) ≫
      Prod.mkHom (DerivedCategory.Q.map
        ((CoefficientTensorChain.complexPullback f R S c).hom.app P))
        (DerivedCategory.Q.map ((CoefficientTensorChain.complexPullback f R S c).hom.app Q)) := by
  ext
  · exact pullback_factors f R S c P
  · exact pullback_factors f R S c Q

end AlgebraicGeometry.Scheme.CoefficientTensorTransport
