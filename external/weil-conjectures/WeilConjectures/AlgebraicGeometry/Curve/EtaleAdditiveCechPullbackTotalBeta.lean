/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechPullbackTotalMap
@[expose] public section
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option autoImplicit false
private theorem restrict_pullback {X Y : Scheme.{u}} (g : Y ⟶ X) (P : X.Opens) :
    X.restrictFunctorΓ.inv.app (op P) ≫ Scheme.Γ.map (morphismRestrict g P).op =
      g.app P ≫ Y.restrictFunctorΓ.inv.app (op (g ⁻¹ᵁ P)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    change X.restrictFunctorΓ.inv.app (op P) ≫ (morphismRestrict g P).appTop = _
    rw [morphismRestrict_appTop]
    dsimp only [Scheme.restrictFunctorΓ]
    simp only [NatIso.ofComponents_inv_app, Functor.mapIso_inv, Iso.op_inv]
    erw [← Category.assoc, g.naturality, Category.assoc, ← Functor.map_comp]
    congr 1

/-- Tuplewise structural pullback coordinates force the beta square for a total map.
Source: Stacks Project, Tags 01FD and 03P2, augmented double-complex diagram.
(blueprint: lem-pbc-etale-additive-cech-pullback-total-beta)
Proof: Unfold beta and apply ht in bidegree (n,0). It suffices to compare
the products before their total inclusion. Project to a tuple y, so the left
side is the resolution augmentation at the source tuple open, followed by
evaluation of alpha and restriction along additiveCechTuplePullback. Evaluate
hα at that source open and use naturality of J.ι along the tuple pullback map.
The result is J.ι at the target tuple open applied to the structural pullback
of its function section. By naturality of restrictFunctorΓ.inv, its transport
from functions on the open subscheme to sections on the open agrees with
restriction along hinter and unitToPushforwardObjUnit. The coordinate equality
in the hypothesis identifies this function with the tuple coordinate of x'.
Lift through ULift and apply J.ι. Product projection extensionality gives the
required equality, hence so does the total inclusion. Empty families give
zero products; degree zero and empty opens satisfy the same functorial
identities. The hypothesis ht is essential: an arbitrary total map need not
preserve the augmentation. -/
theorem additiveCech_pullback_total_beta
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (I : InjectiveResolution X.etaleAdditiveSheaf)
    (J : InjectiveResolution Y.etaleAdditiveSheaf)
    (α : I.cocomplex ⟶
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
        (.up ℕ)).obj J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = Scheme.etaleAdditiveSheafToLowerStar g ≫
      (Etale.lowerStar AddCommGrpCat.{u + 1} g).map (J.ι.f 0))
    (n : ℕ) (t : additiveCechTotal U I ⟶ additiveCechTotal V J)
    (ht : IsAdditiveCechPullbackTotalMap g U V hinter I J α t) :
    ∀ (x : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).X n)
      (x' : (cechOver Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf)).X n),
      (∀ y : Fin (n + 1) → ι,
        cechCoordinate Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf) n y x' =
          (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf).presheaf.map
            (homOfLE (hinter n y)).op
            ((SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom).val.app
              (op (⨅ l, U (y l)))
              (cechCoordinate X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf) n y x))) →
      t.f n (additiveCechBeta U I n x) = additiveCechBeta V J n x' := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    intro x x' hcoord
    unfold additiveCechBeta
    rw [← ConcreteCategory.comp_apply]
    rw [ht n 0 n (by simp)]
    rw [ConcreteCategory.comp_apply]
    congr 1
    apply CategoryTheory.Limits.Concrete.limit_ext (Discrete.functor (fun y : Fin (n + 1) → ι ↦
      (J.cocomplex.X 0).obj.obj
        (op ((additiveCechOpenInclusion Y).obj (∏ᶜ fun l ↦ V (y l))))))
    intro ⟨y⟩
    erw [← ConcreteCategory.comp_apply, additiveCechPullbackBidegree,
      CategoryTheory.Limits.Pi.lift_comp_π,
      ConcreteCategory.comp_apply, CategoryTheory.Limits.Pi.lift_comp_π_apply,
      CategoryTheory.Limits.Pi.lift_comp_π_apply]
    let A := (additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l))
    let B := (additiveCechOpenInclusion Y).obj (∏ᶜ fun l ↦ V (y l))
    let k := additiveCechTuplePullback g U V hinter n y
    let a := (X.restrictFunctorΓ.inv.app (op (∏ᶜ fun l ↦ U (y l)))).hom
      (TopCat.Presheaf.cechComplexFunctorπ U
        (presheafOver X.toSpecΓ (SheafOfModules.unit X.ringCatSheaf)) n y x)
    let b := (Y.restrictFunctorΓ.inv.app (op (∏ᶜ fun l ↦ V (y l)))).hom
      (TopCat.Presheaf.cechComplexFunctorπ V
        (presheafOver Y.toSpecΓ (SheafOfModules.unit Y.ringCatSheaf)) n y x')
    change (J.cocomplex.X 0).obj.map k.op
      ((α.f 0).hom.app (op A) ((I.ι.f 0).hom.app (op A) (ULift.up a))) =
        (J.ι.f 0).hom.app (op B) (ULift.up b)
    have ha := congrArg (fun f ↦ f.hom.app (op A)) hα
    change (I.ι.f 0).hom.app (op A) ≫ (α.f 0).hom.app (op A) =
      (Scheme.etaleAdditiveSheafToLowerStar g).hom.app (op A) ≫
        (J.ι.f 0).hom.app _ at ha
    have he := ConcreteCategory.congr_hom ha (ULift.up a)
    change (α.f 0).hom.app (op A) ((I.ι.f 0).hom.app (op A) (ULift.up a)) =
      (J.ι.f 0).hom.app _
        ((Scheme.etaleAdditiveSheafToLowerStar g).hom.app (op A) (ULift.up a)) at he
    rw [he]
    have hn := (J.ι.f 0).hom.naturality k.op
    have he' := ConcreteCategory.congr_hom hn
      ((Scheme.etaleAdditiveSheafToLowerStar g).hom.app (op A) (ULift.up a))
    change (J.ι.f 0).hom.app (op B)
      (Y.etaleAdditiveSheaf.obj.map k.op
        ((Scheme.etaleAdditiveSheafToLowerStar g).hom.app (op A) (ULift.up a))) =
      (J.cocomplex.X 0).obj.map k.op
        ((J.ι.f 0).hom.app _
          ((Scheme.etaleAdditiveSheafToLowerStar g).hom.app (op A) (ULift.up a))) at he'
    erw [← he']
    apply congrArg ((J.ι.f 0).hom.app (op B))
    apply ULift.ext
    change (Scheme.Γ.map k.left.op).hom
      ((Scheme.Γ.map (CategoryTheory.Limits.pullback.fst A.hom g).op).hom a) = b
    change ((Scheme.Γ.map (CategoryTheory.Limits.pullback.fst A.hom g).op ≫
      Scheme.Γ.map k.left.op).hom a) = b
    rw [← Functor.map_comp, ← op_comp]
    let P := ∏ᶜ fun l ↦ U (y l)
    let Q := ∏ᶜ fun l ↦ V (y l)
    let hp : Q ≤ g ⁻¹ᵁ P := (TopCat.Presheaf.piObj_le_iInf V y).trans
      ((hinter n y).trans (g.preimage_mono (TopCat.Presheaf.iInf_le_piObj U y)))
    have hk : k.left ≫ CategoryTheory.Limits.pullback.fst A.hom g =
        Y.homOfLE hp ≫ morphismRestrict g P := by
      change (Y.homOfLE hp ≫ CategoryTheory.Limits.pullback.lift _ _ _) ≫
        CategoryTheory.Limits.pullback.fst _ _ = _
      simp only [Category.assoc, CategoryTheory.Limits.pullback.lift_fst]
      rfl
    rw [hk, op_comp, Functor.map_comp]
    let c := TopCat.Presheaf.cechComplexFunctorπ U
      (presheafOver X.toSpecΓ (SheafOfModules.unit X.ringCatSheaf)) n y x
    let d := TopCat.Presheaf.cechComplexFunctorπ V
      (presheafOver Y.toSpecΓ (SheafOfModules.unit Y.ringCatSheaf)) n y x'
    change ((X.restrictFunctorΓ.inv.app (op P) ≫
      Scheme.Γ.map (morphismRestrict g P).op ≫
        Scheme.Γ.map (Y.homOfLE hp).op).hom c) =
      (Y.restrictFunctorΓ.inv.app (op Q)).hom d
    rw [← Category.assoc, restrict_pullback]
    have hr := Y.restrictFunctorΓ.inv.naturality (homOfLE hp).op
    change Y.presheaf.map (homOfLE hp).op ≫
        Y.restrictFunctorΓ.inv.app (op Q) =
      Y.restrictFunctorΓ.inv.app (op (g ⁻¹ᵁ P)) ≫
        Scheme.Γ.map (Y.homOfLE hp).op at hr
    rw [Category.assoc, ← hr]
    change (Y.restrictFunctorΓ.inv.app (op Q)).hom
      ((Y.presheaf.map (homOfLE hp).op).hom ((g.app P).hom c)) =
        (Y.restrictFunctorΓ.inv.app (op Q)).hom d
    apply congrArg (Y.restrictFunctorΓ.inv.app (op Q)).hom
    have hc := hcoord y
    change (Y.presheaf.map (homOfLE hp).op).hom ((g.app P).hom c) = d
    dsimp only [cechCoordinate] at hc
    change (Y.presheaf.map (homOfLE (TopCat.Presheaf.iInf_le_piObj V y)).op).hom d =
      (Y.presheaf.map (homOfLE (hinter n y)).op).hom
        ((g.app (⨅ l, U (y l))).hom
          ((X.presheaf.map (homOfLE (TopCat.Presheaf.iInf_le_piObj U y)).op).hom c)) at hc
    let r := (Y.presheaf.map
      (homOfLE (TopCat.Presheaf.iInf_le_piObj V y)).op).hom
    have hinj : Function.Injective r := by
      intro z w h
      have hh := congrArg
        (Y.presheaf.map (homOfLE (TopCat.Presheaf.piObj_le_iInf V y)).op).hom h
      change ((Y.presheaf.map (homOfLE (TopCat.Presheaf.iInf_le_piObj V y)).op ≫
        Y.presheaf.map (homOfLE (TopCat.Presheaf.piObj_le_iInf V y)).op).hom z) =
        ((Y.presheaf.map (homOfLE (TopCat.Presheaf.iInf_le_piObj V y)).op ≫
        Y.presheaf.map (homOfLE (TopCat.Presheaf.piObj_le_iInf V y)).op).hom w) at hh
      rw [← Functor.map_comp, ← op_comp] at hh
      have hi : homOfLE (TopCat.Presheaf.piObj_le_iInf V y) ≫
        homOfLE (TopCat.Presheaf.iInf_le_piObj V y) = 𝟙 _ := Subsingleton.elim _ _
      rw [hi, op_id, Y.presheaf.map_id] at hh
      exact hh
    apply hinj
    change (Y.presheaf.map (homOfLE (TopCat.Presheaf.iInf_le_piObj V y)).op).hom
      ((Y.presheaf.map (homOfLE hp).op).hom ((g.app P).hom c)) =
        (Y.presheaf.map (homOfLE (TopCat.Presheaf.iInf_le_piObj V y)).op).hom d
    rw [hc]
    have hn := g.naturality (homOfLE (TopCat.Presheaf.iInf_le_piObj U y)).op
    have hm :
        g.app P ≫ Y.presheaf.map (homOfLE hp).op ≫
          Y.presheaf.map (homOfLE (TopCat.Presheaf.iInf_le_piObj V y)).op =
        X.presheaf.map (homOfLE (TopCat.Presheaf.iInf_le_piObj U y)).op ≫
          g.app (⨅ l, U (y l)) ≫ Y.presheaf.map (homOfLE (hinter n y)).op := by
      conv_rhs => rw [← Category.assoc, hn, Category.assoc]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 2
    exact congrArg (fun f ↦ f.hom (show Γ(X, P) from c)) hm

end AlgebraicGeometry.Scheme.Modules
