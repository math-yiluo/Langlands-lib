/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleModuleStalkSpecialization
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleStalkSpecialization
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm

/-!
# Comparing module specialization with strict-local abelian specialization

## References

* Stacks Project, Tags 0GJ2 and 0GKD, the geometric-germ construction
* Tag 0GKV, case (a), coefficient comparison
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem pullback_germ
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) :
    ∀ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : X.Etale)
        (ū : (pointSmallEtale (y ≫ f)).fiber.obj U),
        ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G).hom.app
              (op U) ≫
            (pointSmallEtale y).toPresheafFiber (f.Etale.obj U)
              ((pointSmallEtaleFiberEtaleIso f y).inv.app U ū)
              ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj G).obj ≫
            ((Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} f y).app G).hom =
          (pointSmallEtale (y ≫ f)).toPresheafFiber U ū G.obj := by
  intro G U ū
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv _).1
  simp only [Etale.upperStarCompSheafFiberIso, Iso.app_inv, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_assoc]
  rw [show (pointSmallEtale y).sheafFiber.map _ =
    (pointSmallEtale y).presheafFiber.map _ from rfl,
    GrothendieckTopology.Point.toPresheafFiber_naturality]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ f) AddCommGrpCat.{u + 1}
      (X.smallGrothendieckTopology (P := @Etale))
      (Y.smallGrothendieckTopology (P := @Etale)))
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f) G
  have huU := NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (op U)
  rw [← Category.assoc, ← huU]
  rfl

private theorem strictLocal_germ
    {S : Scheme.{u}}
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ξ) ⟶ strictHenselizationScheme s)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    :
  ∀ (j : SmallModel.{u} (strictHenselizationNeighbourhoods s))
    (v : (pointSmallEtale (t ≫ strictHenselizationStructuralMap s)).fiber.obj
      ((AffineEtale.Spec S).obj
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1)),
    v.left = t ≫ (strictHenselizationCone s).π.app (op (op j)) ≫
      Spec.map (ΓSpecIso
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj
          j).1.left.unop).inv →
    (pointSmallEtale s).toPresheafFiber
        ((AffineEtale.Spec S).obj
          ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).2
        G.obj ≫ Etale.etaleStalkSpecialization s t G =
      (pointSmallEtale (t ≫ strictHenselizationStructuralMap s)).toPresheafFiber
        ((AffineEtale.Spec S).obj
          ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        v G.obj := by
  intro j v hv
  let g := strictHenselizationStructuralMap s
  let U := (AffineEtale.Spec S).obj
    ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1
  let H := (Etale.upperStar AddCommGrpCat.{u + 1} g).obj G
  let T : (strictHenselizationScheme s).Etale := Scheme.Etale.mk (𝟙 _)
  let x : (pointSmallEtale t).fiber.obj T := Over.homMk t (by change t ≫ 𝟙 _ = t; simp)
  have hrestr := (Classical.choose_spec
    ((Etale.strictLocalSectionCone s).existsUnique_restriction G)).1 j
  change (pointSmallEtale s).toPresheafFiber U
      ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).2
      G.obj ≫ _ = _ at hrestr
  unfold Etale.etaleStalkSpecialization
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, hrestr]
  unfold Etale.PointedEtaleSectionCone.restriction
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have hpoint : (pointSmallEtale t).fiber.map
      (Etale.strictLocalNeighbourhoodSection s j) x =
      (pointSmallEtaleFiberEtaleIso g t).inv.app U v := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [pointSmallEtaleFiberEtaleIso_inv_app_left_fst]
      change t ≫ (pullback.lift _ (𝟙 _) _) ≫ pullback.fst U.hom g = v.left
      simp only [pullback.lift_fst]
      exact hv.symm
    · rw [pointSmallEtaleFiberEtaleIso_inv_app_left_snd]
      change t ≫ (pullback.lift _ (𝟙 _) _) ≫ pullback.snd U.hom g = t
      simp only [pullback.lift_snd, Category.comp_id]
  change (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app G).hom.app
      (op U) ≫ H.obj.map (Etale.strictLocalNeighbourhoodSection s j).op) ≫
        (pointSmallEtale t).toPresheafFiber T x H.obj ≫
          (Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} g t).hom.app G = _
  rw [Category.assoc, (pointSmallEtale t).toPresheafFiber_w_assoc, hpoint]
  exact pullback_germ g t G U v

/-- An abelian identification transports invertible strict-local specialization to
bijective specialization on module stalks. -/
theorem Etale.bijective_moduleSpecialization_of_abelianIso
    {S : Scheme.{u}} {R : Type (u + 1)} [CommRing R]
    (M : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} R))
    (A : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (e : (Etale.moduleAbelianForget R S).obj M ≅ A)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme s)
    (h : IsIso (Etale.etaleStalkSpecialization s t A)) :
    Function.Bijective (Scheme.etaleModuleStalkSpecialization s t M) := by
  classical
  let V := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  have : PreservesFilteredColimitsOfSize.{u, u} V :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let H := (Etale.moduleAbelianForget R S).obj M
  let w := t ≫ strictHenselizationStructuralMap s
  let cs := ((pointSmallEtale s).sheafFiberCompIso V).app M
  let ct := ((pointSmallEtale w).sheafFiberCompIso V).app M
  let es := cs.symm ≪≫ (pointSmallEtale s).sheafFiber.mapIso e
  let et := ct.symm ≪≫ (pointSmallEtale w).sheafFiber.mapIso e
  let r := Scheme.etaleModuleStalkSpecialization s t M
  have heq : V.map r ≫ et.hom = es.hom ≫ Etale.etaleStalkSpecialization s t A := by
    apply (cancel_epi cs.hom).mp
    simp only [es, et, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_assoc]
    let N := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
      strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
        (fun n : (pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)
    have : N.Initial := (strictHenselization_properties s).1
    let c := ((pointSmallEtale s).presheafFiberCocone H.obj).whisker N.op
    have hc : IsColimit c :=
      (Functor.Final.isColimitWhiskerEquiv N.op _).symm
        ((pointSmallEtale s).isColimitPresheafFiberCocone H.obj)
    apply hc.hom_ext
    intro j
    let U := (AffineEtale.Spec S).obj
      ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j.unop).1
    let x := ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj
      j.unop).2
    let v : (pointSmallEtale w).fiber.obj U :=
      Over.homMk (t ≫ (strictHenselizationCone s).π.app (op j) ≫
        Spec.map (ΓSpecIso
          (((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj
            j.unop).1.left.unop)).inv) (by
        dsimp [U, w]
        rw [Category.assoc, Category.assoc,
          ((exists_strictHenselizationStructuralMap s).choose_spec j.unop)]
        rfl)
    have hs : (pointSmallEtale s).toPresheafFiber U x H.obj ≫ cs.hom =
        V.map ((pointSmallEtale s).toPresheafFiber U x M.obj) :=
      (pointSmallEtale s).toPresheafFiber_presheafFiberCompIso_hom_app V U x M.obj
    have ht : (pointSmallEtale w).toPresheafFiber U v H.obj ≫ ct.hom =
        V.map ((pointSmallEtale w).toPresheafFiber U v M.obj) :=
      (pointSmallEtale w).toPresheafFiber_presheafFiberCompIso_hom_app V U v M.obj
    have hm : (pointSmallEtale s).toPresheafFiber U x M.obj ≫ r =
        (pointSmallEtale w).toPresheafFiber U v M.obj :=
      (Classical.choose_spec
        (existsUnique_etaleModuleStalkSpecialization s t M)).1 j.unop v rfl
    have ha := strictLocal_germ s t A j.unop v rfl
    change (pointSmallEtale s).toPresheafFiber U x H.obj ≫ cs.hom ≫ V.map r ≫
        ct.inv ≫ (pointSmallEtale w).sheafFiber.map e.hom =
      (pointSmallEtale s).toPresheafFiber U x H.obj ≫
        (pointSmallEtale s).sheafFiber.map e.hom ≫ Etale.etaleStalkSpecialization s t A
    calc
      _ = V.map ((pointSmallEtale s).toPresheafFiber U x M.obj) ≫ V.map r ≫
          ct.inv ≫ (pointSmallEtale w).sheafFiber.map e.hom := by
        rw [← Category.assoc, ← Category.assoc, ← Category.assoc, hs]
        simp only [Category.assoc]
      _ = V.map ((pointSmallEtale w).toPresheafFiber U v M.obj) ≫
          ct.inv ≫ (pointSmallEtale w).sheafFiber.map e.hom := by
        rw [← V.map_comp_assoc, hm]
      _ = (pointSmallEtale w).toPresheafFiber U v H.obj ≫
          (pointSmallEtale w).sheafFiber.map e.hom := by
        rw [← ht, Category.assoc, Iso.hom_inv_id_assoc]
      _ = e.hom.hom.app (op U) ≫ (pointSmallEtale w).toPresheafFiber U v A.obj := by
        exact (pointSmallEtale w).toPresheafFiber_naturality e.hom.hom U v
      _ = _ := by
        have hn : (pointSmallEtale s).toPresheafFiber U x H.obj ≫
            (pointSmallEtale s).sheafFiber.map e.hom =
            e.hom.hom.app (op U) ≫ (pointSmallEtale s).toPresheafFiber U x A.obj :=
          (pointSmallEtale s).toPresheafFiber_naturality e.hom.hom U x
        rw [← Category.assoc, hn, Category.assoc]
        exact congrArg (e.hom.hom.app (op U) ≫ ·) ha.symm
  have : IsIso (V.map r ≫ et.hom) := by rw [heq]; infer_instance
  have : IsIso (V.map r) := IsIso.of_isIso_comp_right _ et.hom
  have : IsIso r := isIso_of_reflects_iso r V
  exact ConcreteCategory.bijective_of_isIso r

end AlgebraicGeometry
