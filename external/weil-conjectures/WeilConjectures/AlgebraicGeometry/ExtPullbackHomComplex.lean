/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import WeilConjectures.CategoryTheory.ExtExactFunctorCocycle
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact

/-! # Pullback on the Hom complexes of constant sheaves

Source: Stacks Project, Tag 06XR and Tag 01F8, equations 01F9 and 01FA.
-/

@[expose] public section

universe u v w w'
open CategoryTheory CochainComplex HomComplex Limits
namespace AlgebraicGeometry.SheafPullbackResolution
open Scheme Etale

set_option backward.defeqAttrib.useBackward true in
/-- Apply an additive functor to cochains, then compose with the two supplied maps. -/
noncomputable def homPullbackMap
    {C : Type w} {D : Type w'} [Category.{v} C] [Category.{v} D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasZeroObject D]
    (L : C ⥤ D) [L.Additive] {A : C} {A' : D} (α : A' ⟶ L.obj A)
    (K : CochainComplex C ℤ) (K' : CochainComplex D ℤ)
    (φ : (L.mapHomologicalComplex (.up ℤ)).obj K ⟶ K') :
    HomComplex ((singleFunctor _ 0).obj A) K ⟶
      HomComplex ((singleFunctor _ 0).obj A') K' where
  f n := AddCommGrpCat.ofHom
    { toFun := fun a ↦ Cochain.fromSingleMk
        (α ≫ L.map (Cochain.fromSingleEquiv (zero_add n) a) ≫ φ.f n) (zero_add n)
      map_zero' := by simp
      map_add' := by
        intro a b
        simp [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp] }
  comm' i j hij := by
    ext a
    obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective a i (zero_add i)
    change δ i j (Cochain.fromSingleMk
        (α ≫ L.map (Cochain.fromSingleEquiv (zero_add i)
          (Cochain.fromSingleMk a (zero_add i))) ≫ φ.f i) (zero_add i)) =
      Cochain.fromSingleMk (α ≫ L.map (Cochain.fromSingleEquiv (zero_add j)
        (δ i j (Cochain.fromSingleMk a (zero_add i)))) ≫ φ.f j) (zero_add j)
    rw [Cochain.fromSingleEquiv_fromSingleMk,
      Cochain.δ_fromSingleMk _ _ j j (zero_add j),
      Cochain.δ_fromSingleMk _ _ j j (zero_add j),
      Cochain.fromSingleEquiv_fromSingleMk, Functor.map_comp]
    congr 1
    simpa only [Category.assoc, Functor.mapHomologicalComplex_obj_d] using
      congrArg (fun f ↦ α ≫ L.map a ≫ f) (φ.comm i j)

private theorem homologyMap_apply_of_data
    {S T : ShortComplex AddCommGrpCat.{v}} [S.HasHomology] [T.HasHomology]
    (f : S ⟶ T) (hS : S.LeftHomologyData) (hT : T.LeftHomologyData)
    (γ : ShortComplex.LeftHomologyMapData f hS hT) (x : hS.K) :
    (ShortComplex.homologyMap f) (hS.homologyIso.inv (hS.π x)) =
      hT.homologyIso.inv (hT.π (γ.φK x)) := by
  have hm : hS.homologyIso.inv ≫ ShortComplex.homologyMap f =
      γ.φH ≫ hT.homologyIso.inv := by
    rw [γ.homologyMap_eq]
    simp only [Iso.inv_hom_id_assoc]
  have hπ := ConcreteCategory.congr_hom γ.commπ x
  simp only [ConcreteCategory.comp_apply] at hπ
  have hh := ConcreteCategory.congr_hom hm (hS.π x)
  simp only [ConcreteCategory.comp_apply] at hh
  exact hh.trans (congrArg (fun z ↦ hT.homologyIso.inv z) hπ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem homologyMap_mk
    {C : Type w} {D : Type w'} [Category.{v} C] [Category.{v} D]
    [Preadditive C] [Preadditive D]
    {K L : CochainComplex C ℤ} {K' L' : CochainComplex D ℤ}
    (c : HomComplex K L ⟶ HomComplex K' L') (n : ℤ)
    (x : Cocycle K L n) (y : Cocycle K' L' n)
    (h : (c.f n) (x : Cochain K L n) = (y : Cochain K' L' n)) :
    HomologicalComplex.homologyMap c n ((leftHomologyData K L n).homologyIso.inv
      (CohomologyClass.mk x)) =
      (leftHomologyData K' L' n).homologyIso.inv (CohomologyClass.mk y) := by
  let γ := ShortComplex.leftHomologyMapData
    ((HomologicalComplex.shortComplexFunctor _ _ n).map c)
    (leftHomologyData K L n) (leftHomologyData K' L' n)
  have hK : γ.φK x = y := by
    apply Cocycle.ext
    have hh := ConcreteCategory.congr_hom γ.commi x
    change ((show Cocycle K' L' n from γ.φK x) : Cochain K' L' n) =
      (c.f n) (x : Cochain K L n) at hh
    exact hh.trans h
  have hh := homologyMap_apply_of_data
    ((HomologicalComplex.shortComplexFunctor _ _ n).map c)
    (leftHomologyData K L n) (leftHomologyData K' L' n) γ x
  change HomologicalComplex.homologyMap c n
      ((leftHomologyData K L n).homologyIso.inv (CohomologyClass.mk x)) =
    (leftHomologyData K' L' n).homologyIso.inv (CohomologyClass.mk (γ.φK x)) at hh
  simpa only [hK] using hh


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ext_homComplex_naturality
    {C : Type w} {D : Type w'} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] [HasExt.{v} C] [HasExt.{v} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {A B : C} {A' : D} (α : A' ⟶ L.obj A)
    (R : InjectiveResolution B) (R' : InjectiveResolution (L.obj B))
    (φ : (L.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex ⟶ R'.cochainComplex)
    (hφ : Nonempty (Homotopy
      ((L.mapHomologicalComplex (.up ℤ)).map R.ι' ≫ φ)
      ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).hom.app B ≫ R'.ι')))
    (q : ℕ) (e : Abelian.Ext A B q) :
    HomologicalComplex.homologyMap (homPullbackMap L α _ _ φ) (q : ℤ)
      ((leftHomologyData _ R.cochainComplex (q : ℤ)).homologyIso.inv
        (R.extEquivCohomologyClass e)) =
    (leftHomologyData _ R'.cochainComplex (q : ℤ)).homologyIso.inv
      (R'.extEquivCohomologyClass
        ((Abelian.Ext.mk₀ α).comp (e.mapExactFunctor L) (zero_add q))) := by
  obtain ⟨x, hx⟩ := CohomologyClass.mk_surjective (R.extEquivCohomologyClass e)
  have he : e = R.extEquivCohomologyClass.symm (.mk x) := by
    rw [hx, Equiv.symm_apply_apply]
  subst e
  obtain ⟨a, ha, rfl⟩ := Cocycle.fromSingleMk_surjective x (q : ℤ)
    (zero_add (q : ℤ)) ((q : ℤ) + 1) rfl
  have ha' : (α ≫ L.map a ≫ φ.f (q : ℤ)) ≫
      R'.cochainComplex.d (q : ℤ) ((q : ℤ) + 1) = 0 := by
    have hc := φ.comm (q : ℤ) ((q : ℤ) + 1)
    dsimp only [Functor.mapHomologicalComplex_obj_d] at hc
    simp only [Category.assoc, hc, ← L.map_comp_assoc, ha, L.map_zero,
      zero_comp, comp_zero]
  have hr := InjectiveResolution.ext_mapExactFunctor_cocycle L α R R' φ hφ q a ha ha'
  rw [Equiv.apply_symm_apply, hr, Equiv.apply_symm_apply]
  apply homologyMap_mk
  change Cochain.fromSingleMk
    (α ≫ L.map (Cochain.fromSingleEquiv (zero_add (q : ℤ))
      (Cochain.fromSingleMk a (zero_add (q : ℤ)))) ≫ φ.f (q : ℤ)) (zero_add (q : ℤ)) =
    Cochain.fromSingleMk (α ≫ L.map a ≫ φ.f (q : ℤ)) (zero_add (q : ℤ))
  rw [Cochain.fromSingleEquiv_fromSingleMk]


/-- Ext pullback on the unevaluated Hom complex of a chosen injective resolution.
Source: Stacks Project, Tag 06XR; Tag 01F8, equations 01F9 and 01FA.
(blueprint: lem-weil-pbc-ext-pullback-hom-complex)

Proof: Write a class as a cocycle into the chosen resolution, using the
Ext/resolution equivalence. Its inverse sends it to the roof whose right arrow
is the augmentation. Apply the exact inverse-image functor to the roof and
precompose with the constant-sheaf comparison. The supplied augmentation
homotopy makes the localized composite of the pulled-back augmentation and φ
identical to the target augmentation. Cancel that invertible augmentation.
The resulting roof is the class of the cochain obtained by applying inverse
image degreewise and composing with φ. This is homPullbackMap by its explicit
formula. Passing from cocycles modulo boundaries to the homology of the Hom
complex gives the square below. The argument includes degree zero and zero
objects; it uses no injectivity of the pulled-back resolution. -/
theorem extPullback_homComplex {X X' : Scheme.{u}} (g : X' ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (φ : ((upperStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℤ)).obj
      (injectiveResolution G).cochainComplex ⟶
      (injectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G)).cochainComplex)
    (hφ : Nonempty (Homotopy
      (((upperStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℤ)).map
        (injectiveResolution G).ι' ≫ φ)
      ((HomologicalComplex.singleMapHomologicalComplex
        (upperStar AddCommGrpCat.{u + 1} g) (.up ℤ) 0).hom.app G ≫
        (injectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G)).ι'))) :
    let R := injectiveResolution G
    let R' := injectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G)
    R.extAddEquivCohomologyClass.toAddCommGrpIso.hom ≫
        (leftHomologyData _ (injectiveResolution G).cochainComplex (q : ℤ)).homologyIso.inv ≫
        HomologicalComplex.homologyMap (homPullbackMap (upperStar AddCommGrpCat.{u + 1} g)
          ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).inv.app
            (AddCommGrpCat.of (ULift.{u + 1} ℤ))) _ _ φ) (q : ℤ) =
      AddCommGrpCat.ofHom (cohomologyMap g G q) ≫
        R'.extAddEquivCohomologyClass.toAddCommGrpIso.hom ≫
        (leftHomologyData _
          (injectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G)).cochainComplex
          (q : ℤ)).homologyIso.inv := by
  dsimp only
  apply AddCommGrpCat.ext
  intro e
  simp only [ConcreteCategory.comp_apply, AddEquiv.toAddCommGrpIso_hom,
    AddEquiv.toAddMonoidHom_eq_coe]
  exact ext_homComplex_naturality (upperStar AddCommGrpCat.{u + 1} g)
    ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).inv.app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (injectiveResolution G)
    (injectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G)) φ hφ q e

end AlgebraicGeometry.SheafPullbackResolution
