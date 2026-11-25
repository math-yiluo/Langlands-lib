/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CyclicDerivedHomComparisonMap
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension
import WeilConjectures.AlgebraicGeometry.AbelianRepresentableGeneratorCoherence

/-! # Naturality of free-representable cohomology comparison

Source: Stacks Project, Tag 03Q8, and the free-sheaf adjunction.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
private lemma plusHomExt_precomp {Y : Scheme.{u}}
    {A B F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (a : A ⟶ B) (q : ℕ)
    (ξ : (DerivedCategory.Plus.singleFunctor _ 0).obj B ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧) :
    abelianPlusHomExtEquiv A F q ((DerivedCategory.Plus.singleFunctor _ 0).map a ≫ ξ) =
      (Abelian.Ext.mk₀ a).comp (abelianPlusHomExtEquiv B F q ξ) (zero_add q) := by
  apply (Abelian.Ext.homAddEquiv).injective
  simp only [Abelian.Ext.homAddEquiv_apply, ← Abelian.Ext.singleFunctor_map_comp_hom]
  let C := Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}
  let I : DerivedCategory.Plus C ⥤ DerivedCategory C := DerivedCategory.Plus.ι
  let j := DerivedCategory.Plus.singleFunctorιIso C 0
  let i := (I.commShiftIso (q : ℤ)).app
    ((DerivedCategory.Plus.singleFunctor C 0).obj F)
  unfold abelianPlusHomExtEquiv
  simp only [AddEquiv.trans_apply]
  rw [← Abelian.Ext.homAddEquiv_apply, AddEquiv.apply_symm_apply,
    ← Abelian.Ext.homAddEquiv_apply, AddEquiv.apply_symm_apply]
  change j.inv.app A ≫ I.map ((DerivedCategory.Plus.singleFunctor C 0).map a ≫ ξ) ≫
    i.hom = (DerivedCategory.singleFunctor C 0).map a ≫
      (j.inv.app B ≫ I.map ξ ≫ i.hom)
  rw [Functor.map_comp]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun t ↦ t ≫ I.map ξ ≫ i.hom) (j.inv.naturality a).symm

/-- Naturality of the free-representable comparison before coefficient conversion.
Source: Stacks Project, Tag 03Q8 and the free-sheaf adjunction.
(blueprint: lem-sbc-abelian-representable-cohomology-map-naturality).

Proof: Expand the Ext comparison. Naturality of the inverse-image map on Ext,
together with the universal-section identity and associativity of Ext
precomposition, identifies restriction by `v` with pullback along its base
change. The derived single-object inclusion and exact-functor comparisons are
natural in the source arrow.
-/
theorem abelianRepresentableCohomologyMap_naturality {X Y : Scheme.{u}}
    (h : Y ⟶ X) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    let P := (uliftYoneda.{u + 1} ⋙
      (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
      presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      upperStar AddCommGrpCat.{u + 1} h ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj
          (((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧)
    ∀ (W V : X.Etale) (v : V ⟶ W) (ξ : P.obj (op W)),
      let g := pullback.map h V.hom h W.hom (𝟙 Y) v.left (𝟙 X) (by simp) (by simp)
      let i := upperStarComp AddCommGrpCat.{u + 1} g (pullback.fst h W.hom)
        (pullback.fst h V.hom) (by simp [g])
      Sheaf.H.map (i.inv.app F) q
          (cohomologyMap g _ q (abelianRepresentableCohomologyMap h F q W ξ)) =
        abelianRepresentableCohomologyMap h F q V (P.map v.op ξ) := by
  dsimp only
  intro W V v ξ
  let L := upperStar AddCommGrpCat.{u + 1} (pullback.fst h W.hom)
  let H := upperStar AddCommGrpCat.{u + 1} (pullback.fst h V.hom)
  let g := pullback.map h V.hom h W.hom (𝟙 Y) v.left (𝟙 X) (by simp) (by simp)
  let G := upperStar AddCommGrpCat.{u + 1} g
  let i := upperStarComp AddCommGrpCat.{u + 1} g (pullback.fst h W.hom)
    (pullback.fst h V.hom) (by simp [g])
  let a := (upperStar AddCommGrpCat.{u + 1} h).map ((abelianRepresentable X).map v)
  let k := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).inv.app
    (AddCommGrpCat.of (ULift ℤ))
  let x := abelianPlusHomExtEquiv _ F q ξ
  change ((Abelian.Ext.mk₀ k).comp
      (((Abelian.Ext.mk₀ (abelianRepresentableGenerator h W)).comp
        (x.mapExactFunctor L) (zero_add q)).mapExactFunctor G) (zero_add q)).comp
      (Abelian.Ext.mk₀ (i.inv.app F)) (add_zero q) =
    (Abelian.Ext.mk₀ (abelianRepresentableGenerator h V)).comp
      ((abelianPlusHomExtEquiv _ F q
        ((DerivedCategory.Plus.singleFunctor _ 0).map a ≫ ξ)).mapExactFunctor H) (zero_add q)
  rw [plusHomExt_precomp]
  rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.mk₀_comp_mk₀_assoc]
  rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.mk₀_comp_mk₀_assoc]
  have hc := Abelian.Ext.mapExactFunctor_comp_mk₀_eq_sheaf L G H i x
  have hc' := congrArg (fun y ↦
    ((Abelian.Ext.mk₀ (abelianRepresentableGenerator h V ≫ H.map a)).comp y
      (zero_add q)).comp (Abelian.Ext.mk₀ (i.inv.app F)) (add_zero q)) hc
  simp only [Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀_assoc] at hc'
  simp only [Abelian.Ext.mk₀_comp_mk₀, Iso.hom_inv_id_app,
    Abelian.Ext.comp_mk₀_id, Category.assoc] at hc'
  erw [show abelianRepresentableGenerator h V ≫ H.map a ≫ i.hom.app _ =
      k ≫ G.map (abelianRepresentableGenerator h W) from
        abelianRepresentableGenerator_coherence h W V v] at hc'
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero]
  exact hc'.symm

end AlgebraicGeometry.Etale
