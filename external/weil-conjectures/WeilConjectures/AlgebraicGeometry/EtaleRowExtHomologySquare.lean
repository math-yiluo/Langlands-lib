/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SheafHExtResolutionSectionsIso
public import WeilConjectures.AlgebraicGeometry.ExtPullbackHomComplex
import WeilConjectures.CategoryTheory.ExtCoefficientCocycle

/-! # Ext coefficient naturality before sections evaluation

Source: Stacks Project, Tags 06XR, 01F8 (equations 01F9/01FA), and 08J6.
(blueprint: lem-weil-pbc-row-ext-homology-square).
-/

@[expose] public section

universe uNatural vLevel w w'
open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex Abelian
namespace AlgebraicGeometry.Etale
open Scheme

private theorem homologyMap_apply_of_data
    {S T : ShortComplex AddCommGrpCat.{vLevel}} [S.HasHomology] [T.HasHomology]
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
    {C : Type w} {D : Type w'} [Category.{vLevel} C] [Category.{vLevel} D]
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
    {C : Type w} {D : Type w'} [Category.{vLevel} C] [Category.{vLevel} D]
    [Abelian C] [Abelian D] [HasExt.{vLevel} C] [HasExt.{vLevel} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {A B : C} {A' B' : D} (α : A' ⟶ L.obj A)
    (R : InjectiveResolution B) (R' : InjectiveResolution B') (v : L.obj B ⟶ B')
    (φ : (L.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex ⟶ R'.cochainComplex)
    (hφ : Nonempty (Homotopy
      ((L.mapHomologicalComplex (.up ℤ)).map R.ι' ≫ φ)
      ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).hom.app B ≫
        (singleFunctor D 0).map v ≫ R'.ι')))
    (q : ℕ) (e : Abelian.Ext A B q) :
    HomologicalComplex.homologyMap (SheafPullbackResolution.homPullbackMap L α _ _ φ) (q : ℤ)
      ((leftHomologyData _ R.cochainComplex (q : ℤ)).homologyIso.inv
        (R.extEquivCohomologyClass e)) =
    (leftHomologyData _ R'.cochainComplex (q : ℤ)).homologyIso.inv
      (R'.extEquivCohomologyClass
        (((Abelian.Ext.mk₀ α).comp (e.mapExactFunctor L) (zero_add q)).comp
          (Abelian.Ext.mk₀ v) (add_zero q))) := by
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
  have hr := InjectiveResolution.ext_mapExactFunctor_coefficient_cocycle L α R R' v φ hφ q a ha ha'
  rw [Equiv.apply_symm_apply, hr, Equiv.apply_symm_apply]
  apply homologyMap_mk
  change Cochain.fromSingleMk
    (α ≫ L.map (Cochain.fromSingleEquiv (zero_add (q : ℤ))
      (Cochain.fromSingleMk a (zero_add (q : ℤ)))) ≫ φ.f (q : ℤ)) (zero_add (q : ℤ)) =
    Cochain.fromSingleMk (α ≫ L.map a ≫ φ.f (q : ℤ)) (zero_add (q : ℤ))
  rw [Cochain.fromSingleEquiv_fromSingleMk]



set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pullback and the coefficient map on Ext are computed on the unevaluated Hom complex.
Source: Stacks Project, Tags 06XR, 01F8 (equations 01F9/01FA), and 08J6.
(blueprint: lem-weil-pbc-row-ext-homology-square).

Proof. Put L = f inverse image and let α be the inverse constant-integer-sheaf
comparison. Represent an Ext class by a cohomology class using the resolution
R, then by a cocycle, then by a single cocycle a in degree p. The chain-map
identity for ψ and L's additivity imply that α;L(a);ψ in degree p is a cocycle.
The augmentation equality yields Homotopy.ofEq hψ. Apply
InjectiveResolution.ext_mapExactFunctor_coefficient_cocycle to these two cocycles:
the target Ext class is precomposition by α, exact-functor pullback of the source
class, and postcomposition by v. On short complexes, the left homology map data
commute with both the inclusion of cocycles and the quotient projection. Hence
the Hom-complex homology map sends the class of a to the class of α;L(a);ψ.
Surjectivity of CohomologyClass.mk and Cocycle.fromSingleMk makes this calculation
apply to every Ext class. The definition of homPullbackMap is exactly the displayed
cochain calculation. Rewrite Sheaf.H.map_apply and cohomologyMap_apply and use
extensionality of abelian-group morphisms to obtain the square. This statement
has no sections functor or evaluation map, so it does not include the separate
component evaluation square. Degree zero, zero coefficients, zero sheaves, and
empty schemes use the same cocycle and quotient formulas. -/
theorem ceExtHomologySquare {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
    (G' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
    (R : InjectiveResolution G) (R' : InjectiveResolution G')
    (v : (upperStar AddCommGrpCat.{uNatural + 1} f).obj G ⟶ G')
    (ψ : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj R.cochainComplex ⟶ R'.cochainComplex)
    (hψ : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).map R.ι' ≫ ψ =
      (HomologicalComplex.singleMapHomologicalComplex
        (upperStar AddCommGrpCat.{uNatural + 1} f) (ComplexShape.up ℤ) 0).hom.app G ≫
      (CochainComplex.singleFunctor _ 0).map v ≫ R'.ι')
    (p : ℕ) :
    R.extAddEquivCohomologyClass.toAddCommGrpIso.hom ≫
        (leftHomologyData _ R.cochainComplex (p : ℤ)).homologyIso.inv ≫
        HomologicalComplex.homologyMap
          (SheafPullbackResolution.homPullbackMap
            (upperStar AddCommGrpCat.{uNatural + 1} f)
            ((upperStarConstantSheafIso AddCommGrpCat.{uNatural + 1} f).inv.app
              (AddCommGrpCat.of (ULift.{uNatural + 1} ℤ)))
            R.cochainComplex R'.cochainComplex ψ) (p : ℤ) =
      AddCommGrpCat.ofHom ((Sheaf.H.map v p).comp (cohomologyMap f G p)) ≫
        R'.extAddEquivCohomologyClass.toAddCommGrpIso.hom ≫
        (leftHomologyData _ R'.cochainComplex (p : ℤ)).homologyIso.inv := by
  let L := upperStar AddCommGrpCat.{uNatural + 1} f
  let α := (upperStarConstantSheafIso AddCommGrpCat.{uNatural + 1} f).inv.app
    (AddCommGrpCat.of (ULift.{uNatural + 1} ℤ))
  have hhψ := Homotopy.ofEq hψ
  apply AddCommGrpCat.ext
  intro e
  simp only [ConcreteCategory.comp_apply, AddEquiv.toAddCommGrpIso_hom,
    AddEquiv.toAddMonoidHom_eq_coe, ConcreteCategory.hom_ofHom, AddMonoidHom.comp_apply,
    Sheaf.H.map_apply, cohomologyMap_apply]
  exact ext_homComplex_naturality L α R R' v ψ ⟨hhψ⟩ p e

end AlgebraicGeometry.Etale
