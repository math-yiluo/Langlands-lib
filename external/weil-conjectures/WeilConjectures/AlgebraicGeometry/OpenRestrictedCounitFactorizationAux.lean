/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedTensorComplexIso
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedComparisonComposition
import all WeilConjectures.AlgebraicGeometry.AffineSpectrumCompositionCounitSquare
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange
attribute [local irreducible] Scheme.Modules.tensorPullbackCompositionIso
  Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] DerivedCategory
  HomotopyCategory DerivedCategory.Q DerivedCategory.Qh

private abbrev schemeModulesDerived
    [d : ∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (Y : Scheme.{u}) : HasDerivedCategory.{w} Y.Modules := d Y

attribute [local instance] schemeModulesDerived

private theorem open_restriction_counit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    (openRestrictionRepresentativeIso j P).hom ≫
        (counit j).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (openTensorRestrictionIso j).symm (.up ℤ)).hom.app P) := by
  classical
  let T := Scheme.Modules.tensorPullback j
  have : T.Additive := tensorPullbackAdditive.{u, w} j
  let R := openRestrictionFunctor j
  let θ : T ≅ R := openTensorRestrictionIso j
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_natIso θ.symm
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_natIso θ.symm
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)
  have : (derivedPullback j).IsLeftDerivedFunctor (counit j) W :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) j
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  let e := Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback j) (counit j)
    T.mapDerivedCategoryFactorsh.hom W
  have he : e.inv.app (DerivedCategory.Q.obj P) ≫
      (counit j).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      T.mapDerivedCategoryFactors.hom.app P := by
    have h := Functor.leftDerivedNatTrans_app T.mapDerivedCategory (derivedPullback j)
      T.mapDerivedCategoryFactorsh.hom (counit j) W (𝟙 _)
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
    simp only [NatTrans.id_app, Category.comp_id] at h
    change e.inv.app (DerivedCategory.Q.obj P) ≫ _ = _ at h
    rw [Functor.mapDerivedCategoryFactorsh_hom_app] at h
    change e.inv.app (DerivedCategory.Q.obj P) ≫ _ =
      T.mapDerivedCategory.map (𝟙 _) ≫ T.mapDerivedCategoryFactors.hom.app P ≫
        𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) at h
    erw [T.mapDerivedCategory.map_id,
      (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).map_id] at h
    erw [Category.id_comp, Category.comp_id] at h
    exact h.trans (Category.comp_id _)
  change (R.mapDerivedCategoryFactors.inv.app P ≫
    (Functor.mapDerivedCategoryNatIso θ).inv.app (DerivedCategory.Q.obj P) ≫
      e.inv.app (DerivedCategory.Q.obj P)) ≫ _ = _
  rw [Category.assoc, Category.assoc, he]
  have hn := Functor.mapDerivedCategoryNatIso_fac θ.symm P
  change (Functor.mapDerivedCategoryNatIso θ).inv.app (DerivedCategory.Q.obj P) ≫
    T.mapDerivedCategoryFactors.hom.app P = _ at hn
  rw [hn]
  simp only [Iso.inv_hom_id_app_assoc]
  rfl

private theorem open_composition_counit_square
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (k : X' ⟶ X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    openRestrictedCompositionMap k U (DerivedCategory.Q.obj P) ≫
        (derivedPullback (pullback.fst k U.ι)).map
          ((counit k).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        (counit (pullback.fst k U.ι)).app ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj P)) =
      (derivedPullback (pullback.snd k U.ι)).map
          ((counit U.ι).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        (counit (pullback.snd k U.ι)).app ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((Scheme.Modules.tensorPullback U.ι).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
          (Scheme.Modules.tensorPullbackCompositionIso (pullback.snd k U.ι) U.ι
            (pullback.fst k U.ι ≫ k) pullback.condition.symm) (.up ℤ)).app P)).inv ≫
        (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
          (Scheme.Modules.tensorPullbackCompositionIso (pullback.fst k U.ι) k
            (pullback.fst k U.ι ≫ k) rfl) (.up ℤ)).app P)).hom := by
  let c₁ := (selectedComposition (pullback.snd k U.ι) U.ι ≪≫
    eqToIso (congrArg (fun l ↦ derivedPullback.{u, w} l) pullback.condition.symm)).app
      (DerivedCategory.Q.obj P)
  let c₂ := (selectedComposition (pullback.fst k U.ι) k).app (DerivedCategory.Q.obj P)
  have h₁ := composition_factorization_transport (pullback.snd k U.ι) U.ι
    (pullback.fst k U.ι ≫ k) pullback.condition.symm P
  have h₂ := composition_factorization (pullback.fst k U.ι) k P
  have h := compare_counit_factorizations c₁ c₂ _ _
    ((counit (pullback.fst k U.ι ≫ k)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) _ _ h₁ h₂
  simpa only [openRestrictedCompositionMap, c₁, c₂, selectedComposition,
    Iso.app_hom, Iso.app_inv, Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    eqToIso.hom, eqToHom_app] using h.symm

private theorem tensor_square_inverse
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (k : X' ⟶ X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    ((Scheme.Modules.tensorPullback (pullback.snd k U.ι)).mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex (openTensorRestrictionIso U.ι) (.up ℤ)).inv.app P) ≫
      ((NatIso.mapHomologicalComplex
        (Scheme.Modules.tensorPullbackCompositionIso (pullback.snd k U.ι) U.ι
          (pullback.fst k U.ι ≫ k) pullback.condition.symm) (.up ℤ)).app P).inv ≫
      ((NatIso.mapHomologicalComplex
        (Scheme.Modules.tensorPullbackCompositionIso (pullback.fst k U.ι) k
          (pullback.fst k U.ι ≫ k) rfl) (.up ℤ)).app P).hom ≫
      (NatIso.mapHomologicalComplex (openTensorRestrictionIso (pullback.fst k U.ι))
        (.up ℤ)).hom.app
        (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj P) =
      (openTensorRestrictionComplexIso k U P).inv := by
  apply HomologicalComplex.hom_ext
  intro n
  simp [openTensorRestrictionComplexIso, openTensorRestrictionSquareIso,
    NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex]

private theorem restriction_counit_glue
    {V : Type*} [Category V] {A B C D E F G H I J : V}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (e : D ⟶ E) (t : E ⟶ F)
    (f : B ⟶ G) (g : G ⟶ H) (i : H ⟶ I) (j : I ⟶ E)
    (v : A ⟶ G) (l : A ⟶ J) (m : J ⟶ H) (n : J ⟶ F) (d : D ≅ F)
    (hc : b ≫ c ≫ e = f ≫ g ≫ i ≫ j) (ha : a ≫ f = v)
    (hn : v ≫ g = l ≫ m) (hd : e ≫ t = d.hom) (ht : m ≫ i ≫ j ≫ t = n) :
    a ≫ b ≫ c = l ≫ n ≫ d.inv := by
  apply (cancel_mono d.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hd, reassoc_of% hc, reassoc_of% ha, reassoc_of% hn, ht]

private theorem counit_iso_inverse
    {V : Type*} [Category V] {A B C : V} (e : A ≅ B) (t : C ≅ A) (ε : B ⟶ C)
    (h : e.hom ≫ ε = t.inv) : ε ≫ t.hom = e.inv := by
  apply (cancel_epi e.hom).1
  rw [← Category.assoc, h]
  simp only [Iso.inv_hom_id, Iso.hom_inv_id]

attribute [local implicit_reducible] Scheme.Modules TopCat.Sheaf

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] openRestrictionRepresentativeIso openRestrictedCompositionMap
  openRestrictedTensorDerivedIso openTensorRestrictionComplexIso openTensorRestrictionSquareIso
  openTensorRestrictionIso counit

/-- Auxiliary counit compatibility equation used to derive the strict factorization.
Source: Stacks Project, Tags 0D5S and 0D5U.
(blueprint: new-open-restricted-counit-compatibility-aux).
The equation follows by evaluating the defining left-derived composition
factorization and the exact restriction adjunction, then identifying the
remaining tensor comparisons with `openRestrictedTensorDerivedIso`.
-/
private theorem openRestricted_counit_compatibility_aux_private
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    (derivedPullback (pullback.snd g' U.ι)).map (openRestrictionRepresentativeIso U.ι P).hom ≫
        openRestrictedCompositionMap g' U (DerivedCategory.Q.obj P) ≫
        (derivedPullback (pullback.fst g' U.ι)).map
          ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      (counit (pullback.snd g' U.ι)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        (openRestrictedTensorDerivedIso g' U P).inv := by
  let p := pullback.fst g' U.ι
  let q := pullback.snd g' U.ι
  let TP := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
  let R := ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P
  let T := ((Scheme.Modules.tensorPullback U.ι).mapHomologicalComplex (.up ℤ)).obj P
  let eR := openRestrictionRepresentativeIso U.ι P
  let eP := openRestrictionRepresentativeIso p TP
  let θ := (NatIso.mapHomologicalComplex (openTensorRestrictionIso U.ι) (.up ℤ)).app P
  let θP := (NatIso.mapHomologicalComplex (openTensorRestrictionIso p) (.up ℤ)).app TP
  let b₁ := DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
    (Scheme.Modules.tensorPullbackCompositionIso q U.ι (p ≫ g')
      pullback.condition.symm) (.up ℤ)).app P)
  let b₂ := DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
    (Scheme.Modules.tensorPullbackCompositionIso p g' (p ≫ g') rfl) (.up ℤ)).app P)
  let εj := (counit U.ι).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  let εp := (counit p).app ((HomotopyCategory.quotient _ (.up ℤ)).obj TP)
  let εqT := (counit q).app ((HomotopyCategory.quotient _ (.up ℤ)).obj T)
  let εqR := (counit q).app ((HomotopyCategory.quotient _ (.up ℤ)).obj R)
  let m := (derivedPullback p).map
    ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
  let b := openRestrictedCompositionMap g' U (DerivedCategory.Q.obj P)
  have hs : b ≫ m ≫ εp = (derivedPullback q).map εj ≫ εqT ≫ b₁.inv ≫ b₂.hom :=
    open_composition_counit_square g' U P
  have hj : eR.hom ≫ εj = DerivedCategory.Q.map θ.inv :=
    open_restriction_counit U.ι P
  have hp : eP.hom ≫ εp = (DerivedCategory.Q.mapIso θP).inv :=
    open_restriction_counit p TP
  have hp' := counit_iso_inverse eP (DerivedCategory.Q.mapIso θP) εp hp
  have hn := (counit q).naturality
    ((HomotopyCategory.quotient _ (.up ℤ)).map θ.inv)
  change (derivedPullback q).map (DerivedCategory.Q.map θ.inv) ≫ εqT =
    εqR ≫ DerivedCategory.Q.map
      (((Scheme.Modules.tensorPullback q).mapHomologicalComplex (.up ℤ)).map θ.inv) at hn
  have ht := congrArg DerivedCategory.Q.map (tensor_square_inverse g' U P)
  simp only [Functor.map_comp] at ht
  change DerivedCategory.Q.map
      (((Scheme.Modules.tensorPullback q).mapHomologicalComplex (.up ℤ)).map θ.inv) ≫
    b₁.inv ≫ b₂.hom ≫ (DerivedCategory.Q.mapIso θP).hom =
      (DerivedCategory.Q.mapIso (openTensorRestrictionComplexIso g' U P)).inv at ht
  have hj' : (derivedPullback q).map eR.hom ≫ (derivedPullback q).map εj =
      (derivedPullback q).map (DerivedCategory.Q.map θ.inv) := by
    exact ((derivedPullback q).map_comp eR.hom εj).symm.trans
      (congrArg (derivedPullback q).map hj)
  have h := restriction_counit_glue ((derivedPullback q).map eR.hom) b m εp
    (DerivedCategory.Q.mapIso θP).hom ((derivedPullback q).map εj) εqT b₁.inv b₂.hom
    ((derivedPullback q).map (DerivedCategory.Q.map θ.inv)) εqR
    (DerivedCategory.Q.map
      (((Scheme.Modules.tensorPullback q).mapHomologicalComplex (.up ℤ)).map θ.inv))
    (DerivedCategory.Q.mapIso (openTensorRestrictionComplexIso g' U P)).inv eP.symm
    hs hj' hn hp' ht
  simp only [openRestrictedTensorDerivedIso, Iso.trans_inv, Iso.symm_inv]
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      exact h

/-- Public export of the private `openRestricted_counit_compatibility_aux_private`
(used by `import all` importers; linter.privateModule). -/
alias openRestricted_counit_compatibility_aux := openRestricted_counit_compatibility_aux_private

end AlgebraicGeometry.SingleComplexBaseChange
