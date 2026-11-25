/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
/-! # A derived adjunction counit on cochain representatives

Source: Stacks Project, Cohomology on Sites, Tag 06YY; the derived unit identity
of `CategoryTheory.Adjunction.derivedη_fac_app`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u u₁ u₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
open scoped CategoryTheory.Functor
namespace CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
variable {C : Type u₁} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive] [E.PreservesKFlatQuasiIso]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]

private theorem derived_unit_cochain (adj : E ⊣ U) (X : CochainComplex C ℤ) :
    let b := adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
    let q₀ := (DerivedCategory.quotientCompQhIso C).app X
    let q₁ := (DerivedCategory.quotientCompQhIso D).app
      ((E.mapHomologicalComplex (.up ℤ)).obj X)
    let ε := E.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj X)
    b.unit.app (DerivedCategory.Q.obj X) ≫
        U.mapDerivedCategory.map (E.leftDerivedFunctor.map q₀.inv ≫ ε ≫ q₁.hom) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app X) ≫
        U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj X) := by
  let b := adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
  let q₀ := (DerivedCategory.quotientCompQhIso C).app X
  let q₁ := (DerivedCategory.quotientCompQhIso D).app
    ((E.mapHomologicalComplex (.up ℤ)).obj X)
  let q₂ := (DerivedCategory.quotientCompQhIso C).app
    ((U.mapHomologicalComplex (.up ℤ)).obj ((E.mapHomologicalComplex (.up ℤ)).obj X))
  let ε := E.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj X)
  let d := E.leftDerivedFunctor.map q₀.inv ≫ ε ≫ q₁.hom
  have hfac := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ))
    E.leftDerivedFunctorCounit U.rightDerivedFunctorUnit
    ((HomotopyCategory.quotient _ (.up ℤ)).obj X)
  have ht : b.unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
      U.mapDerivedCategory.map (E.leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
      U.mapDerivedCategoryFactorsh.hom.app
        ((E.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) := by
    simp only [b, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Category.assoc]
    erw [← U.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
    erw [← Category.assoc, hfac]
    have hβ := NatTrans.congr_app
      U.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
      ((E.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj X))
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hβ
    rw [Category.assoc]
    erw [reassoc_of% hβ]
    simp only [Iso.inv_hom_id_app]
    erw [Category.comp_id]
  have hu := U.mapDerivedCategoryFactorsh_hom_app
    ((E.mapHomologicalComplex (.up ℤ)).obj X)
  have hquot : DerivedCategory.Qh.map
      ((U.mapHomotopyCategoryFactors (.up ℤ)).inv.app
        ((E.mapHomologicalComplex (.up ℤ)).obj X)) = 𝟙 _ := by
    change DerivedCategory.Qh.map (𝟙 _) = 𝟙 _
    exact DerivedCategory.Qh.map_id _
  rw [hquot] at hu
  erw [Category.comp_id] at hu
  have hu' : U.mapDerivedCategory.map q₁.hom ≫
      U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj X) =
      U.mapDerivedCategoryFactorsh.hom.app
        ((E.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫ q₂.hom := by
    have h := congrArg (fun z ↦ z ≫ q₂.hom) hu
    change U.mapDerivedCategoryFactorsh.hom.app
      ((E.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫ q₂.hom =
      (U.mapDerivedCategory.map q₁.hom ≫
        U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj X) ≫
          q₂.inv) ≫ q₂.hom at h
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
    exact h.symm
  change b.unit.app (DerivedCategory.Q.obj X) ≫ U.mapDerivedCategory.map d = _
  apply (cancel_mono (U.mapDerivedCategoryFactors.hom.app
    ((E.mapHomologicalComplex (.up ℤ)).obj X))).mp
  apply (cancel_epi q₀.hom).mp
  have hn := b.unit.naturality q₀.hom
  change q₀.hom ≫ b.unit.app (DerivedCategory.Q.obj X) =
    b.unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
      U.mapDerivedCategory.map (E.leftDerivedFunctor.map q₀.hom) at hn
  have hq := DerivedCategory.quotientCompQhIso_hom_naturality
    ((adj.mapHomologicalComplex (.up ℤ)).unit.app X)
  have hd : E.leftDerivedFunctor.map q₀.hom ≫ d = ε ≫ q₁.hom := by
    change (E.leftDerivedFunctor.mapIso q₀).hom ≫
      ((E.leftDerivedFunctor.mapIso q₀).inv ≫ ε ≫ q₁.hom) = _
    exact Iso.hom_inv_id_assoc _ _
  have hdnat : q₀.hom ≫ b.unit.app (DerivedCategory.Q.obj X) ≫
      U.mapDerivedCategory.map d =
    b.unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
      U.mapDerivedCategory.map ε ≫ U.mapDerivedCategory.map q₁.hom := by
    calc
      _ = b.unit.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
        U.mapDerivedCategory.map (E.leftDerivedFunctor.map q₀.hom) ≫
          U.mapDerivedCategory.map d := by
        simpa only [Category.assoc] using congrArg
          (fun z ↦ z ≫ U.mapDerivedCategory.map d) hn
      _ = _ := by
        rw [← U.mapDerivedCategory.map_comp, hd, Functor.map_comp]
  calc
    _ = b.unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
        U.mapDerivedCategory.map ε ≫ U.mapDerivedCategory.map q₁.hom ≫
          U.mapDerivedCategoryFactors.hom.app
            ((E.mapHomologicalComplex (.up ℤ)).obj X) := by
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫
        U.mapDerivedCategoryFactors.hom.app
          ((E.mapHomologicalComplex (.up ℤ)).obj X)) hdnat
    _ = b.unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
        U.mapDerivedCategory.map ε ≫
        U.mapDerivedCategoryFactorsh.hom.app
          ((E.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫ q₂.hom := by
      exact congrArg (fun z ↦ b.unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫
        U.mapDerivedCategory.map ε ≫ z) hu'
    _ = DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≫ q₂.hom := by
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ q₂.hom) ht
    _ = q₀.hom ≫ DerivedCategory.Q.map
        ((adj.mapHomologicalComplex (.up ℤ)).unit.app X) := by
      erw [Adjunction.mapHomotopyCategory_unit_app_quotient]
      exact hq
    _ = _ := by
      simp only [Category.assoc, Iso.inv_hom_id_app]
      erw [Category.comp_id]

/-- Transporting the left-derived counit to a chosen adjunction gives the transpose
of the ordinary cochain unit, including both quotient comparison isomorphisms.
Source: Stacks Project, Tag 06YY, derived scalar adjunction
(blueprint: lem-derived-adjoint-cochain-counit).
Proof: the derived-unit identity on the homotopy category identifies the composite
of the derived unit with the left-derived counit and the right-derived unit.
Exactness of the right adjoint identifies its right-derived functor with the
levelwise functor. Naturality of the quotient comparison passes the identity to
cochain representatives. The unit identity for uniqueness of left adjoints then
identifies its transpose with the chosen-adjunction counit displayed here. -/
theorem Adjunction.leftDerivedCochainCounit {L : DerivedCategory C ⥤ DerivedCategory D}
    (adj : E ⊣ U) (ad : L ⊣ U.mapDerivedCategory) (X : CochainComplex C ℤ) :
    let b := adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
    let e := ad.leftAdjointUniq b
    let q₀ := (DerivedCategory.quotientCompQhIso C).app X
    let q₁ := (DerivedCategory.quotientCompQhIso D).app
      ((E.mapHomologicalComplex (.up ℤ)).obj X)
    let ε := E.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj X)
    e.hom.app (DerivedCategory.Q.obj X) ≫
        E.leftDerivedFunctor.map q₀.inv ≫ ε ≫ q₁.hom =
      (ad.homEquiv _ _).symm
        (DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app X) ≫
          U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj X)) := by
  dsimp only
  apply (ad.homEquiv _ _).injective
  erw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc,
    Adjunction.unit_leftAdjointUniq_hom_app]
  simpa only [Functor.map_comp, Category.assoc] using derived_unit_cochain E U adj X

end CategoryTheory
