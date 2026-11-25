/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SpecializationCospecializationArrows
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationCanonicalMap

/-! # Specialization to the distinguished closed lift

Source: Stacks Project, Tag 0GJ2, the pointed-neighbourhood construction.
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

private theorem germ_transport
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {s t : Spec (.of Ω) ⟶ S} (h : t = s)
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : S.Etale)
    (v : (pointSmallEtale t).fiber.obj U) (w : (pointSmallEtale s).fiber.obj U)
    (hv : v.left = w.left) :
    (pointSmallEtale t).toPresheafFiber U v F.obj ≫
      eqToHom (congrArg (fun p ↦ (pointSmallEtale p).sheafFiber.obj F) h) =
    (pointSmallEtale s).toPresheafFiber U w F.obj := by
  cases h
  have : v = w := Over.OverMorphism.ext hv
  subst w
  simp

/-- At the distinguished closed lift the specialization is the original germ,
with only the transport of its geometric point.
Source: Stacks Project, Tag 0GJ2 and Tag 04HX.
(blueprint: lem-weil-pbc-closed-lift-stalk-specialization). -/
theorem Etale.etaleStalkSpecialization_closed
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S)
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    etaleStalkSpecialization s
        (Spec.map (CommRingCat.ofHom (strictHenselizationRingPointEvaluation s))) F ≫
      eqToHom (congrArg (fun p ↦ (pointSmallEtale p).sheafFiber.obj F)
        (strictHenselizationClosedLift_over s)) = 𝟙 _ := by
  let y := Spec.map (CommRingCat.ofHom (strictHenselizationRingPointEvaluation s))
  let N := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
    strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
      (fun n : (pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)
  have : N.Initial := (strictHenselization_properties s).1
  let c := ((pointSmallEtale s).presheafFiberCocone F.obj).whisker N.op
  let hc : IsColimit c :=
    (Functor.Final.isColimitWhiskerEquiv N.op _).symm
      ((pointSmallEtale s).isColimitPresheafFiberCocone F.obj)
  apply hc.hom_ext
  intro j
  let U := (N.obj j.unop).1
  let w := (N.obj j.unop).2
  let v : (pointSmallEtale (y ≫ strictHenselizationStructuralMap s)).fiber.obj U :=
    Over.homMk w.left (w.w.trans (strictHenselizationClosedLift_over s).symm)
  have hv : v.left = y ≫ (strictHenselizationCone s).π.app (op (op j.unop)) ≫
      Spec.map (ΓSpecIso
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj
          j.unop).1.left.unop).inv := by
    change ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj
      j.unop).2.left = _
    simpa only [y, Scheme.isoSpec_Spec_inv] using
      (strictHenselizationRingPointEvaluation_pointed s j.unop).symm
  change (pointSmallEtale s).toPresheafFiber U w F.obj ≫ _ = _
  rw [← Category.assoc]
  erw [strictLocal_germ s y F j.unop v hv]
  exact (germ_transport (strictHenselizationClosedLift_over s) F U v w rfl).trans
    (Category.comp_id _).symm

private theorem exactDerived_transport
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    {I : Type*} (F : I → C ⥤ D) [∀ i, (F i).Additive]
    [∀ i, PreservesFiniteLimits (F i)] [∀ i, PreservesFiniteColimits (F i)]
    {i j : I} (h : i = j) (τ : F i ⟶ F j)
    (hτ : ∀ A, τ.app A = eqToHom (congrArg (fun k ↦ (F k).obj A) h))
    (K : _root_.DerivedCategory.Plus C) :
    (F i).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app K ≫
        (Functor.rightDerivedFunctorPlusNatTrans τ).app K ≫
        (F j).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app K =
      eqToHom (congrArg (fun k ↦ (F k).mapDerivedCategoryPlus.obj K) h) := by
  cases h
  have he : τ = 𝟙 (F i) := by
    ext A
    simpa using hτ A
  subst τ
  simp [Functor.rightDerivedFunctorPlusNatTrans, NatTrans.mapHomotopyCategoryPlus_id]

/-- Derived specialization to the distinguished closed lift is the canonical transport.
Source: Stacks Project, Tag 0GJ2 and Tag 04HX.
(blueprint: lem-weil-pbc-closed-lift-stalk-specialization). -/
theorem Etale.derivedEtaleStalkSpecialization_closed
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S)
    (K : _root_.DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (derivedEtaleStalkSpecialization s
        (Spec.map (CommRingCat.ofHom (strictHenselizationRingPointEvaluation s)))).app K =
      eqToHom (congrArg (fun p : Spec (.of Ω) ⟶ S ↦
        (pointSmallEtale p).sheafFiber.mapDerivedCategoryPlus.obj K)
          (strictHenselizationClosedLift_over s).symm) := by
  let y := Spec.map (CommRingCat.ofHom (strictHenselizationRingPointEvaluation s))
  let F := fun p : Spec (.of Ω) ⟶ S ↦
    (pointSmallEtale p).sheafFiber (A := AddCommGrpCat.{u + 1})
  let h := (strictHenselizationClosedLift_over s).symm
  have hτ (A : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
      (etaleStalkSpecializationNatTrans s y).app A =
        eqToHom (congrArg (fun p ↦ (F p).obj A) h) := by
    apply (cancel_mono (eqToHom (congrArg
      (fun p ↦ (pointSmallEtale p).sheafFiber.obj A)
      (strictHenselizationClosedLift_over s)))).1
    simpa only [F, h, y, etaleStalkSpecializationNatTrans, eqToHom_trans,
      eqToHom_refl] using etaleStalkSpecialization_closed s A
  exact exactDerived_transport F h (etaleStalkSpecializationNatTrans s y) hτ K

end AlgebraicGeometry
