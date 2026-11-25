/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.ScalarTensorOrdinaryPullback
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackDescentData
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # The restricted derived scalar mate on representatives

Source: Stacks Project, Tags 03EK, 06YY, 07A4 and 07A6.
(blueprint: lem-sfb-scalar-mate-restriction-counit-route).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.DerivedScalarMate
universe u₀ v₀ w₀
section
variable {A B A' B' : Type u₀}
  [Category.{v₀} A] [Category.{v₀} B] [Category.{v₀} A'] [Category.{v₀} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{w₀} A] [HasDerivedCategory.{w₀} B]
  [HasDerivedCategory.{w₀} A'] [HasDerivedCategory.{w₀} B']
  (E : A ⥤ B) (E' : A' ⥤ B') [E.Additive] [E'.Additive]
  (R : B ⥤ A) (R' : B' ⥤ A') [R.Additive] [R'.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  (a : E ⊣ R) (a' : E' ⊣ R')
  (L : DerivedCategory A ⥤ DerivedCategory B)
  (L' : DerivedCategory A' ⥤ DerivedCategory B')
  (ad : L ⊣ R.mapDerivedCategory.{w₀, w₀}) (ad' : L' ⊣ R'.mapDerivedCategory.{w₀, w₀})
  (ε : DerivedCategory.Q.{w₀} ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w₀})
  (ε' : DerivedCategory.Q.{w₀} ⋙ L' ⟶ E'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w₀})
  (F : A ⥤ A') (G : B ⥤ B') [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (ρ : R ⋙ F ≅ G ⋙ R')
  (ρd : R.mapDerivedCategory.{w₀, w₀} ⋙ F.mapDerivedCategory.{w₀, w₀} ≅
    G.mapDerivedCategory.{w₀, w₀} ⋙ R'.mapDerivedCategory.{w₀, w₀})
  (hρ : ∀ K : CochainComplex B ℤ,
    ρd.hom.app (DerivedCategory.Q.{w₀}.obj K) ≫
      R'.mapDerivedCategory.{w₀, w₀}.map (G.mapDerivedCategoryFactors.{w₀, w₀}.hom.app K) ≫
      R'.mapDerivedCategoryFactors.{w₀, w₀}.hom.app
        ((G.mapHomologicalComplex (.up ℤ)).obj K) =
    F.mapDerivedCategory.{w₀, w₀}.map (R.mapDerivedCategoryFactors.{w₀, w₀}.hom.app K) ≫
      F.mapDerivedCategoryFactors.{w₀, w₀}.hom.app
        ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.{w₀}.map ((NatTrans.mapHomologicalComplex ρ.hom (.up ℤ)).app K))
  (e : E ⋙ G ≅ F ⋙ E')
  (β : F.mapDerivedCategory.{w₀, w₀} ⋙ L' ⟶ L ⋙ G.mapDerivedCategory.{w₀, w₀})
  (hβ : ∀ X, ad'.unit.app (F.mapDerivedCategory.{w₀, w₀}.obj X) ≫
    R'.mapDerivedCategory.{w₀, w₀}.map (β.app X) =
    F.mapDerivedCategory.{w₀, w₀}.map (ad.unit.app X) ≫
      ρd.hom.app (L.obj X))
  (P : CochainComplex A ℤ)
  (hunit : ad.unit.app (DerivedCategory.Q.{w₀}.obj P) ≫
    R.mapDerivedCategory.{w₀, w₀}.map (ε.app P) ≫
    R.mapDerivedCategoryFactors.{w₀, w₀}.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.{w₀}.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P))
  (hunit' : ad'.unit.app (DerivedCategory.Q.{w₀}.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
    R'.mapDerivedCategory.{w₀, w₀}.map (ε'.app ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
    R'.mapDerivedCategoryFactors.{w₀, w₀}.hom.app
      ((E'.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) =
    DerivedCategory.Q.{w₀}.map ((a'.mapHomologicalComplex (.up ℤ)).unit.app
      ((F.mapHomologicalComplex (.up ℤ)).obj P)))
  (he : ∀ X, F.map (a.unit.app X) ≫ ρ.hom.app (E.obj X) ≫
    R'.map (e.hom.app X) = a'.unit.app (F.obj X))
include hρ hβ hunit hunit' he in
private theorem mate_computes_resolving :
    β.app (DerivedCategory.Q.{w₀}.obj P) ≫
      G.mapDerivedCategory.{w₀, w₀}.map (ε.app P) ≫
      G.mapDerivedCategoryFactors.{w₀, w₀}.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.{w₀}.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) =
    L'.map (F.mapDerivedCategoryFactors.{w₀, w₀}.hom.app P) ≫
      ε'.app ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  let Ec := E.mapHomologicalComplex (.up ℤ)
  let E'c := E'.mapHomologicalComplex (.up ℤ)
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Gc := G.mapHomologicalComplex (.up ℤ)
  let Rc := R.mapHomologicalComplex (.up ℤ)
  let R'c := R'.mapHomologicalComplex (.up ℤ)
  let ρc := NatIso.mapHomologicalComplex ρ (.up ℤ)
  let ec := NatIso.mapHomologicalComplex e (.up ℤ)
  have hec : Fc.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      ρc.hom.app (Ec.obj P) ≫ R'c.map (ec.hom.app P) =
        (a'.mapHomologicalComplex (.up ℤ)).unit.app (Fc.obj P) := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact he (P.X i)
  apply (ad'.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp]
  apply (cancel_mono
    (R'.mapDerivedCategoryFactors.{w₀, w₀}.hom.app (E'c.obj (Fc.obj P)))).1
  simp only [Category.assoc]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, hβ]
  simp only [Category.assoc]
  rw [← reassoc_of% (ρd.hom.naturality (ε.app P))]
  erw [R'.mapDerivedCategoryFactors.{w₀, w₀}.hom.naturality (ec.hom.app P)]
  erw [reassoc_of% (hρ (Ec.obj P))]
  simp only [← CategoryTheory.Functor.map_comp_assoc]
  rw [hunit]
  rw [reassoc_of% (F.mapDerivedCategoryFactors.{w₀, w₀}.hom.naturality
    ((a.mapHomologicalComplex (.up ℤ)).unit.app P))]
  simp only [← CategoryTheory.Functor.map_comp_assoc]
  change F.mapDerivedCategoryFactors.{w₀, w₀}.hom.app P ≫
    DerivedCategory.Q.{w₀}.map (Fc.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      ρc.hom.app (Ec.obj P)) ≫ DerivedCategory.Q.{w₀}.map (R'c.map (ec.hom.app P)) = _
  rw [← CategoryTheory.Functor.map_comp]
  erw [Category.assoc, hec]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [← reassoc_of% (ad'.unit.naturality (F.mapDerivedCategoryFactors.{w₀, w₀}.hom.app P))]
  erw [hunit']

end

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftAdjoint
  proEtaleRingModulePullback
  SheafOfModules.monoidalCategory ordinaryComplexIso ordinaryTensorIso
  proEtaleRingRestrictionDerivedPullback
set_option backward.defeqAttrib.useBackward true

private theorem scalarCounit_rep {W : Scheme.{u}}
    {A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : A ⟶ B)
    (P : CochainComplex (proEtaleRingModules W A) ℤ)
    (hp : proEtaleFlatRepresentatives W A P) :
    (proEtaleRingDerivedExtensionAdjunction a).unit.app (DerivedCategory.Q.obj P) ≫
      (restriction a).mapDerivedCategory.map
        ((complexCounitNat (proEtaleRingExtension a) (proEtaleRingDerivedExtension a)
          (proEtaleRingDerivedExtensionCounit a)).app P) ≫
      (restriction a).mapDerivedCategoryFactors.hom.app
        (((proEtaleRingExtension a).mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map
      (((proEtaleRingExtensionAdjunction a).mapHomologicalComplex (.up ℤ)).unit.app P) := by
  rw [complexCounitNat_app]
  have hu : ((proEtaleRingExtensionAdjunction a).mapHomologicalComplex (.up ℤ)).unit.app P =
      (NatTrans.mapHomologicalComplex (proEtaleRingExtensionAdjunction a).unit (.up ℤ)).app P := by
    apply HomologicalComplex.Hom.ext
    funext n
    rfl
  rw [hu]
  exact (pbcDerivedScalarAdjunction_exists a).exists.choose_spec P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat (R := A) P).2 hp.1)

private theorem tensorScalarCounit_eq {W : Scheme.{u}}
    {A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : A ⟶ B)
    (P : CochainComplex (proEtaleRingModules W A) ℤ) :
    tensorScalarCounit a P =
      (restriction a).mapDerivedCategory.map
        ((complexCounitNat (proEtaleRingExtension a) (proEtaleRingDerivedExtension a)
          (proEtaleRingDerivedExtensionCounit a)).app P) ≫
      (restriction a).mapDerivedCategoryFactors.hom.app
        (((proEtaleRingExtension a).mapHomologicalComplex (.up ℤ)).obj P) := by
  rw [complexCounitNat_app]
  unfold tensorScalarCounit reductionComplexCounit
  change _ ≫ (restriction a).mapDerivedCategoryFactorsh.hom.app
    ((HomotopyCategory.quotient _ _).obj
      (((proEtaleRingExtension a).mapHomologicalComplex (.up ℤ)).obj P)) = _
  rw [CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app]
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
    CategoryTheory.Functor.mapHomotopyCategoryFactors]
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id,
    CategoryTheory.Functor.map_id, Category.comp_id,
    CategoryTheory.Functor.map_id, Category.comp_id]
  erw [Category.id_comp]

private theorem scalarMate_counit {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B)
    (χ : proEtaleRingExtension a ⋙
      proEtaleRingModulePullback f B (inverseRing f B) (Iso.refl _) ≅
      proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _) ⋙
        proEtaleRingExtension (inverseMap f a))
    (hχ : ∀ M, (proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)).map
        ((proEtaleRingExtensionAdjunction a).unit.app M) ≫
      (proEtaleRingRestrictionPullbackInv f A B (inverseRing f A) (inverseRing f B)
        a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)).app
          ((proEtaleRingExtension a).obj M) ≫
      (restriction (inverseMap f a)).map (χ.hom.app M) =
      (proEtaleRingExtensionAdjunction (inverseMap f a)).unit.app
        ((proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)).obj M))
    (P : CochainComplex (proEtaleRingModules T A) ℤ)
    (hp : proEtaleFlatRepresentatives T A P) :
    let FP := ((proEtaleRingModulePullback f A (inverseRing f A)
      (Iso.refl _)).mapHomologicalComplex (.up ℤ)).obj P
    (scalarPullback f a).hom.app (DerivedCategory.Q.obj P) ≫
      (proEtaleRingDerivedExtension (inverseMap f a)).map
        ((proEtaleRingDerivedPullbackFactors f A (inverseRing f A) (Iso.refl _)).hom.app P) ≫
      (complexCounitNat (proEtaleRingExtension (inverseMap f a))
        (proEtaleRingDerivedExtension (inverseMap f a))
        (proEtaleRingDerivedExtensionCounit (inverseMap f a))).app FP =
    (pull f B).map ((complexCounitNat (proEtaleRingExtension a)
      (proEtaleRingDerivedExtension a) (proEtaleRingDerivedExtensionCounit a)).app P) ≫
      (proEtaleRingDerivedPullbackFactors f B (inverseRing f B) (Iso.refl _)).hom.app
        (((proEtaleRingExtension a).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex χ (.up ℤ)).hom.app P) := by
  dsimp only
  let FA := proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)
  let FB := proEtaleRingModulePullback f B (inverseRing f B) (Iso.refl _)
  let b := proEtaleRingRestrictionPullbackInv f A B (inverseRing f A) (inverseRing f B)
    a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)
  have : IsIso b := proEtaleRingRestrictionPullbackInv_isIso f A B
    (inverseRing f A) (inverseRing f B) a (inverseMap f a)
    (Iso.refl _) (Iso.refl _) (by simp)
  let rho := asIso b
  let bd := proEtaleRingRestrictionDerivedPullback f A B (inverseRing f A) (inverseRing f B)
    a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)
  have hb : bd.inv = (CategoryTheory.Functor.mapDerivedCategorySquareIso rho).hom := by
    unfold bd proEtaleRingRestrictionDerivedPullback
    change (CategoryTheory.Functor.mapDerivedCategorySquareIso rho.symm).inv = _
    have hi : CategoryTheory.Functor.mapDerivedCategorySquareIso rho.symm =
        (CategoryTheory.Functor.mapDerivedCategorySquareIso rho).symm :=
      Iso.ext (CategoryTheory.Functor.square_symm_hom rho)
    simpa only [Iso.symm_inv] using congrArg (fun e ↦ e.inv) hi
  have hmate (X : DerivedCategory (proEtaleRingModules T A)) :
      (proEtaleRingDerivedExtensionAdjunction (inverseMap f a)).unit.app
          ((pull f A).obj X) ≫
        (restriction (inverseMap f a)).mapDerivedCategory.map
          ((scalarPullback f a).inv.app X) =
      (pull f A).map ((proEtaleRingDerivedExtensionAdjunction a).unit.app X) ≫
        (CategoryTheory.Functor.mapDerivedCategorySquareIso rho).hom.app
          ((proEtaleRingDerivedExtension a).obj X) := by
    rw [← hb]
    exact (unit_mateEquiv_symm (proEtaleRingDerivedExtensionAdjunction a)
      (proEtaleRingDerivedExtensionAdjunction (inverseMap f a))
      (TwoSquare.mk _ _ _ _ bd.inv) X).symm
  have h := mate_computes_resolving
    (proEtaleRingExtension a) (proEtaleRingExtension (inverseMap f a))
    (restriction a) (restriction (inverseMap f a))
    (proEtaleRingExtensionAdjunction a) (proEtaleRingExtensionAdjunction (inverseMap f a))
    (proEtaleRingDerivedExtension a) (proEtaleRingDerivedExtension (inverseMap f a))
    (proEtaleRingDerivedExtensionAdjunction a)
    (proEtaleRingDerivedExtensionAdjunction (inverseMap f a))
    (complexCounitNat (proEtaleRingExtension a) (proEtaleRingDerivedExtension a)
      (proEtaleRingDerivedExtensionCounit a))
    (complexCounitNat (proEtaleRingExtension (inverseMap f a))
      (proEtaleRingDerivedExtension (inverseMap f a))
      (proEtaleRingDerivedExtensionCounit (inverseMap f a)))
    FA FB rho (CategoryTheory.Functor.mapDerivedCategorySquareIso rho)
    (fun K ↦ CategoryTheory.Functor.exactSquare_fac rho K) χ
    (scalarPullback f a).inv hmate P
    (scalarCounit_rep a P hp)
    (scalarCounit_rep (inverseMap f a) _
      ((proEtaleTensorPullbackDescentData f A (inverseRing f A) (Iso.refl _)).1 P hp))
    hχ
  apply (cancel_epi ((scalarPullback f a).inv.app (DerivedCategory.Q.obj P))).mp
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  simpa only [Category.assoc, proEtaleRingDerivedPullbackFactors] using h.symm

/-- A unit-normalized ordinary scalar comparison computes the restricted derived mate.
Source: Stacks Tags 06YY and 07A6
(blueprint: lem-sfb-scalar-mate-restriction-counit-route).

Proof: transpose the representative comparison through the derived scalar
adjunction. On the K-flat complexes P and its exact inverse image, the specified
derived units followed by the universal scalar counits are the localized ordinary
units. Naturality of the exact restriction square and the ordinary unit equation
identify the two transposes. Restrict the equality and use naturality of the
restriction localization factors. Expanding tensorScalarCounit gives precisely
the displayed equation. No ordinary tensor-coordinate identification is used. -/
theorem scalarMate_restriction_counit_route {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B)
    (χ : proEtaleRingExtension a ⋙
      proEtaleRingModulePullback f B (inverseRing f B) (Iso.refl _) ≅
      proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _) ⋙
        proEtaleRingExtension (inverseMap f a))
    (hχ : ∀ M, (proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)).map
        ((proEtaleRingExtensionAdjunction a).unit.app M) ≫
      (proEtaleRingRestrictionPullbackInv f A B (inverseRing f A) (inverseRing f B)
        a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)).app
          ((proEtaleRingExtension a).obj M) ≫
      (restriction (inverseMap f a)).map (χ.hom.app M) =
      (proEtaleRingExtensionAdjunction (inverseMap f a)).unit.app
        ((proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)).obj M))
    (P : CochainComplex (proEtaleRingModules T A) ℤ)
    (hp : proEtaleFlatRepresentatives T A P) :
    let FA := proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)
    let rZ := restriction (inverseMap f a)
    let EP := ((proEtaleRingExtension a).mapHomologicalComplex (.up ℤ)).obj P
    (proEtaleRingRestrictionDerivedPullback f A B (inverseRing f A) (inverseRing f B)
        a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)).inv.app
          ((proEtaleRingDerivedExtension a).obj (DerivedCategory.Q.obj P)) ≫
      rZ.mapDerivedCategory.map ((scalarPullback f a).hom.app (DerivedCategory.Q.obj P)) ≫
      rZ.mapDerivedCategory.map ((proEtaleRingDerivedExtension (inverseMap f a)).map
        ((proEtaleRingDerivedPullbackFactors f A (inverseRing f A) (Iso.refl _)).hom.app P)) ≫
      tensorScalarCounit (inverseMap f a) ((FA.mapHomologicalComplex (.up ℤ)).obj P) =
    (pull f A).map (tensorScalarCounit a P) ≫
      (proEtaleRingDerivedPullbackFactors f A (inverseRing f A) (Iso.refl _)).hom.app
        (((restriction a).mapHomologicalComplex (.up ℤ)).obj EP) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (proEtaleRingRestrictionPullbackInv f A B (inverseRing f A) (inverseRing f B)
            a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)) (.up ℤ)).app EP) ≫
      DerivedCategory.Q.map
        ((rZ.mapHomologicalComplex (.up ℤ)).map
          ((CategoryTheory.Functor.mapHomologicalComplexCompIso χ (.up ℤ)
            ).hom.app P)) := by
  dsimp only
  let FA := proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)
  let FB := proEtaleRingModulePullback f B (inverseRing f B) (Iso.refl _)
  let rY := restriction a
  let rX := restriction (inverseMap f a)
  let EP := ((proEtaleRingExtension a).mapHomologicalComplex (.up ℤ)).obj P
  let c := (CategoryTheory.Functor.mapHomologicalComplexCompIso
    χ (.up ℤ)).hom.app P
  let bd := proEtaleRingRestrictionDerivedPullback f A B (inverseRing f A) (inverseRing f B)
    a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)
  let b := proEtaleRingRestrictionPullbackInv f A B (inverseRing f A) (inverseRing f B)
    a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)
  have : IsIso b := proEtaleRingRestrictionPullbackInv_isIso f A B
    (inverseRing f A) (inverseRing f B) a (inverseMap f a)
    (Iso.refl _) (Iso.refl _) (by simp)
  let rho := asIso b
  have hb : bd.inv = (CategoryTheory.Functor.mapDerivedCategorySquareIso rho).hom := by
    unfold bd proEtaleRingRestrictionDerivedPullback
    change (CategoryTheory.Functor.mapDerivedCategorySquareIso rho.symm).inv = _
    have hi : CategoryTheory.Functor.mapDerivedCategorySquareIso rho.symm =
        (CategoryTheory.Functor.mapDerivedCategorySquareIso rho).symm :=
      Iso.ext (CategoryTheory.Functor.square_symm_hom rho)
    simpa only [Iso.symm_inv] using congrArg (fun e ↦ e.inv) hi
  have hfac := CategoryTheory.Functor.exactSquare_fac rho EP
  rw [← hb] at hfac
  rw [tensorScalarCounit_eq, tensorScalarCounit_eq]
  erw [← rX.mapDerivedCategory.map_comp_assoc, ← rX.mapDerivedCategory.map_comp_assoc]
  erw [Category.assoc]
  erw [scalarMate_counit f a χ hχ P hp]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [rX.mapDerivedCategoryFactors.hom.naturality c]
  erw [← reassoc_of% (bd.inv.naturality
    ((complexCounitNat (proEtaleRingExtension a) (proEtaleRingDerivedExtension a)
      (proEtaleRingDerivedExtensionCounit a)).app P))]
  erw [reassoc_of% hfac]
  rfl

end AlgebraicGeometry.Scheme.DerivedScalarMate
