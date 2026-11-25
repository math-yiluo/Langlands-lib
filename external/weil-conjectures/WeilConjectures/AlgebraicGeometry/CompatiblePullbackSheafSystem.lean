/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-! # Compatible pullbacks of a fixed sheaf

Source: Stacks Project, Sites, Tag 03CB, and Etale Cohomology, Tag 09YQ.
(blueprint: lem-weil-pbc-compatible-pullback-sheaf-system).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

private theorem upperStarComp_inv_of_eq_id {X T : Scheme.{u}}
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : X ⟶ T) (h : X ⟶ X) (hh : h = 𝟙 X) (ha : a = h ≫ a) :
    (upperStarComp AddCommGrpCat.{u + 1} h a a ha).inv.app G =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) hh)).hom.app
        ((upperStar AddCommGrpCat.{u + 1} a).obj G) ≫
      (upperStarId AddCommGrpCat.{u + 1} X).hom.app
        ((upperStar AddCommGrpCat.{u + 1} a).obj G) := by
  cases hh
  simpa only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.id_obj,
    Functor.comp_obj, Category.comp_id] using
    congrArg (fun e ↦ e.inv.app G) (upperStarComp_id_left AddCommGrpCat.{u + 1} a)

/-- Canonical pullback comparisons give a sheaf system, identified on a cone with a
constant diagram. No limit or quasi-compactness hypothesis is needed.
Source: Stacks Project, Sites, Tag 03CB (composition of morphisms of sites), and the
compatible inverse-image system in Etale Cohomology, Tag 09YQ.
(blueprint: lem-weil-pbc-compatible-pullback-sheaf-system).

Proof:
1. The transition from i to j is the inverse composition comparison for D.map f.op
   and v i. For an identity map, the left unit law for upperStarComp identifies this
   with upperStarId, including transport along D.map_id.
2. For f : i -> j and g : j -> k, apply the associativity law for upperStarComp to
   D.map g.op, D.map f.op and v i. Transport by D.map_comp and wv, take inverse
   components, and cancel the comparison for the first two maps. This is exactly
   the displayed composition equation for phi.
3. Apply the same calculation to d.pi at j, D.map f.op and v i. The cone equation
   identifies their first composite with d.pi at i. After transport by wLimit, it
   says that the comparison from stage i, followed by the transition and the inverse
   comparison at j, is the identity of vLimit inverse image of G. Thus S is the
   constant diagram with precisely the required comparison maps. -/
theorem compatiblePullbackSheafSystem
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (d : Cone D)
    (T : Scheme.{u}) (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (v : ∀ i : I, D.obj (op i) ⟶ T)
    (wv : ∀ (i j : I) (f : i ⟶ j), v j = D.map f.op ≫ v i)
    (vLimit : d.pt ⟶ T) (wLimit : ∀ i : I, vLimit = d.π.app (op i) ≫ v i) :
    let F := fun i : I ↦ (upperStar AddCommGrpCat.{u + 1} (v i)).obj G
    let φ := fun {i j : I} (f : i ⟶ j) ↦
      (upperStarComp AddCommGrpCat.{u + 1} (D.map f.op) (v i)
        (v j) (wv i j f)).inv.app G
    let K := (upperStar AddCommGrpCat.{u + 1} vLimit).obj G
    let S : I ⥤ Sheaf d.pt.smallEtaleTopology AddCommGrpCat.{u + 1} :=
      (Functor.const I).obj K
    let eS := fun i : I ↦
      (upperStarComp AddCommGrpCat.{u + 1} (d.π.app (op i)) (v i)
        vLimit (wLimit i)).app G
    (∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i)) ∧
    (∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k), φ (f ≫ g) =
      (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
        (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
      (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g) ∧
    (∀ (i j : I) (f : i ⟶ j), S.map f =
      (eS i).hom ≫
      (upperStarComp AddCommGrpCat.{u + 1} (d.π.app (op j)) (D.map f.op)
        (d.π.app (op i)) (d.w f.op).symm).hom.app (F i) ≫
      (upperStar AddCommGrpCat.{u + 1} (d.π.app (op j))).map (φ f) ≫ (eS j).inv) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact upperStarComp_inv_of_eq_id G (v i) (D.map (𝟙 (op i)))
      (D.map_id (op i)) (wv i i (𝟙 i))
  · intro i j k f g
    have h := upperStarComp_hom_app_map_upperStarComp_inv_app
      AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op) (v i)
      (D.map (f ≫ g).op) (v j) (v k) (D.map_comp g.op f.op)
      (wv i j f) (wv i k (f ≫ g)) G
    simpa only [Category.assoc, Iso.app_inv] using
      ((upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (v j)
        (v k) (wv j k g)).app G).eq_comp_inv.mpr h.symm
  · intro i j f
    have h := upperStarComp_hom_app_map_upperStarComp_inv_app
      AddCommGrpCat.{u + 1} (d.π.app (op j)) (D.map f.op) (v i)
      (d.π.app (op i)) (v j) vLimit (d.w f.op).symm (wv i j f) (wLimit i) G
    let ei := (upperStarComp AddCommGrpCat.{u + 1} (d.π.app (op i)) (v i)
      vLimit (wLimit i)).app G
    let ej := (upperStarComp AddCommGrpCat.{u + 1} (d.π.app (op j)) (v j)
      vLimit (wLimit j)).app G
    have h' := congrArg (fun k ↦ ei.hom ≫ k ≫ ej.inv) h
    simpa only [ei, ej, Category.assoc, Iso.app_hom, Iso.app_inv,
      Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, Category.comp_id,
      Functor.const_obj_map] using h'.symm

end AlgebraicGeometry.Etale
