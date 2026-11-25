/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedLiftGenerators
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import all WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedLocalizationSequence
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSpecializationRestrictionSections
import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar

/-! # Closed inverse image on the free closed-lift presentation
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

section AbelianComparison
open CategoryTheory.Functor.sheafPullbackConstruction
variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (F : C ⥤ D) [F.IsContinuous J K]
  {E : Type*} [Category.{u + 1} E] (U : E ⥤ AddCommGrpCat.{u + 1})
  [∀ P : Cᵒᵖ ⥤ E, F.op.HasLeftKanExtension P]
  [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}, F.op.HasLeftKanExtension P]
  [HasWeakSheafify K E] [HasWeakSheafify K AddCommGrpCat.{u + 1}]
  [J.HasSheafCompose U] [K.HasSheafCompose U]
  [K.PreservesSheafification U] [U.PreservesLeftKanExtensions F.op]

private noncomputable def abelianComparison :
    sheafPullback F E J K ⋙ sheafCompose K U ≅
      sheafCompose J U ⋙ sheafPullback F (AddCommGrpCat.{u + 1}) J K :=
  NatIso.ofComponents (fun S ↦
    ((sheafComposeNatIso K U (sheafificationAdjunction K E)
      (sheafificationAdjunction K (AddCommGrpCat.{u + 1}))).app (F.op.lan.obj S.obj)).symm ≪≫
    (presheafToSheaf K (AddCommGrpCat.{u + 1})).mapIso
      ((U.lanCompIsoOfPreserves F.op).app S.obj))
    (by
      intro S T g
      change (presheafToSheaf K E ⋙ sheafCompose K U).map (F.op.lan.map g.hom) ≫
          (sheafComposeNatIso K U (sheafificationAdjunction K E)
            (sheafificationAdjunction K (AddCommGrpCat.{u + 1}))).inv.app _ ≫ _ = _
      rw [(sheafComposeNatIso K U (sheafificationAdjunction K E)
        (sheafificationAdjunction K (AddCommGrpCat.{u + 1}))).inv.naturality_assoc]
      change _ ≫ (presheafToSheaf K (AddCommGrpCat.{u + 1})).map _ ≫
        (presheafToSheaf K (AddCommGrpCat.{u + 1})).map _ = _ ≫
        (presheafToSheaf K (AddCommGrpCat.{u + 1})).map _ ≫
          (presheafToSheaf K (AddCommGrpCat.{u + 1})).map _
      simp only [← Functor.map_comp]
      congr 2
      exact (U.lanCompIsoOfPreserves F.op).hom.naturality g.hom)
private theorem abelianComparison_unit (S : Sheaf J E) :
    (sheafCompose J U).map ((sheafAdjunctionContinuous F E J K).unit.app S) ≫
      (F.sheafPushforwardContinuous (AddCommGrpCat.{u + 1}) J K).map
        ((abelianComparison J K F U).hom.app S) =
      (sheafAdjunctionContinuous F (AddCommGrpCat.{u + 1}) J K).unit.app
        ((sheafCompose J U).obj S) := by
  apply (sheafToPresheaf J (AddCommGrpCat.{u + 1})).map_injective
  simp only [Functor.map_comp]
  change Functor.whiskerRight ((sheafToPresheaf J E).map
      ((sheafAdjunctionContinuous F E J K).unit.app S)) U ≫ _ = _
  simp only [sheafAdjunctionContinuous, sheafPullback,
    Adjunction.map_restrictFullyFaithful_unit_app]
  dsimp only [Functor.comp_obj, Functor.id_obj, Iso.refl_hom, NatTrans.id_app]
  simp only [Category.comp_id]
  simp only [Adjunction.comp_unit_app]
  simp only [Functor.comp_map, ObjectProperty.ι_map,
    ObjectProperty.FullSubcategory.id_hom, Functor.whiskeringLeft_obj_map]
  erw [Functor.whiskerLeft_id', Category.comp_id, Functor.whiskerLeft_id', Category.comp_id]
  change Functor.whiskerRight ((F.op.lanAdjunction E).unit.app S.obj ≫
      Functor.whiskerLeft F.op ((sheafificationAdjunction K E).unit.app _)) U ≫
      Functor.whiskerLeft F.op
        (((sheafComposeNatIso K U (sheafificationAdjunction K E)
          (sheafificationAdjunction K (AddCommGrpCat.{u + 1}))).inv.app _).hom ≫
        ((presheafToSheaf K (AddCommGrpCat.{u + 1})).map
          ((U.lanCompIsoOfPreserves F.op).hom.app S.obj)).hom) =
    (F.op.lanAdjunction (AddCommGrpCat.{u + 1})).unit.app (S.obj ⋙ U) ≫
      Functor.whiskerLeft F.op ((sheafificationAdjunction K (AddCommGrpCat.{u + 1})).unit.app _)
  simp only [Functor.whiskerRight_comp, Functor.whiskerLeft_comp, Category.assoc]
  have hs : Functor.whiskerRight
      ((sheafificationAdjunction K E).unit.app (F.op.lan.obj S.obj)) U ≫
      ((sheafComposeNatIso K U (sheafificationAdjunction K E)
        (sheafificationAdjunction K (AddCommGrpCat.{u + 1}))).inv.app _).hom =
      (sheafificationAdjunction K (AddCommGrpCat.{u + 1})).unit.app (F.op.lan.obj S.obj ⋙ U) := by
    have h := sheafComposeNatTrans_fac K U (sheafificationAdjunction K E)
      (sheafificationAdjunction K (AddCommGrpCat.{u + 1})) (F.op.lan.obj S.obj)
    rw [← h]
    simp only [Category.assoc]
    change _ ≫ ((sheafToPresheaf K (AddCommGrpCat.{u + 1})).map
      ((sheafComposeNatIso K U (sheafificationAdjunction K E)
        (sheafificationAdjunction K (AddCommGrpCat.{u + 1}))).hom.app _) ≫
      (sheafToPresheaf K (AddCommGrpCat.{u + 1})).map _) = _
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    simp
  have hn := (sheafificationAdjunction K (AddCommGrpCat.{u + 1})).unit.naturality
    ((U.lanCompIsoOfPreserves F.op).hom.app S.obj)
  have hk := U.leftKanExtensionCompIsoOfPreserves_hom_fac S.obj F.op
  ext V x
  have hs' := congrArg (fun t ↦ t.app (F.op.obj V)) hs
  have hn' := congrArg (fun t ↦ t.app (F.op.obj V)) hn
  have hk' := congrArg (fun t ↦ t.app V) hk
  simp only [Functor.lanAdjunction_unit] at hs' hn' hk' ⊢
  dsimp [Functor.lanCompIsoOfPreserves, Functor.lanUnit] at hs' hn' hk' ⊢
  simp only [Category.id_comp] at hk'
  have hsx := ConcreteCategory.congr_hom hs'
    ((U.map ((F.op.leftKanExtensionUnit S.obj).app V)) x)
  have hnx := ConcreteCategory.congr_hom hn'
    ((U.map ((F.op.leftKanExtensionUnit S.obj).app V)) x)
  have hkx := ConcreteCategory.congr_hom hk' x
  dsimp at hsx hnx hkx
  exact (congrArg (fun y ↦ (((presheafToSheaf K (AddCommGrpCat.{u + 1})).map
      (U.leftKanExtensionCompIsoOfPreserves S.obj F.op).hom).hom.app (F.op.obj V)) y)
    hsx).trans (hnx.symm.trans (congrArg (fun y ↦
      ((toSheafify K (F.op.leftKanExtension (S.obj ⋙ U))).app (F.op.obj V)) y) hkx))
end AbelianComparison

private theorem module_unit_bijective
    (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}}
    (z : Z ⟶ X) [IsClosedImmersion z] (W : X.ProEt) [IsAffine W.left]
    (hw : ∀ (P Q : Sheaf (ProEt.topology X) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op W)))
    (hs : ∀ x : W.left, ∃ y : ↥(pullback W.hom z),
      Specializes x ((pullback.fst W.hom z) y))
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    Function.Bijective
      (((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) z).unit.app M).hom.app
        (op W)) := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let e := abelianComparison (ProEt.topology X) (ProEt.topology Z)
    (proEtaleBaseChange z) U
  let E := (sheafToPresheaf (ProEt.topology Z) AddCommGrpCat.{u + 1}) ⋙
    (CategoryTheory.evaluation _ _).obj (op ((proEtaleBaseChange z).obj W))
  have he := ConcreteCategory.bijective_of_isIso (E.map (e.hom.app M))
  have hu := abelianComparison_unit (ProEt.topology X) (ProEt.topology Z)
    (proEtaleBaseChange z) U M
  have hb := isIso_proEtaleUnit_sections_of_specialization z W hw hs
  have : IsIso
      (((proEtaleSheafAdjunction z AddCommGrpCat.{u + 1}).unit.app
        ((sheafCompose (ProEt.topology X) U).obj M)).hom.app (op W)) :=
    inferInstanceAs (IsIso (((Functor.whiskerRight
      (proEtaleSheafAdjunction z AddCommGrpCat.{u + 1}).unit
      ((sheafSections (ProEt.topology X) AddCommGrpCat.{u + 1}).obj (op W))).app _)))
  have hbij := ConcreteCategory.bijective_of_isIso
    (((proEtaleSheafAdjunction z AddCommGrpCat.{u + 1}).unit.app
      ((sheafCompose (ProEt.topology X) U).obj M)).hom.app (op W))
  have hcomp := congrArg (fun f ↦ f.hom.app (op W)) hu
  have hbcomp : Function.Bijective
      ((e.hom.app M).hom.app (op ((proEtaleBaseChange z).obj W)) ∘
        (((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) z).unit.app M).hom.app
          (op W))) := by
    rw [← hcomp] at hbij
    change Function.Bijective
      ((e.hom.app M).hom.app (op ((proEtaleBaseChange z).obj W)) ∘
        (((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) z).unit.app M).hom.app
          (op W))) at hbij
    exact hbij
  exact hbcomp.of_comp_left he.1

private theorem augmentation_tests
    (A : Type u) [CommRing A] {X Z : Scheme.{u}} (z : Z ⟶ X)
    (M N : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (f g : M ⟶ N)
    (h : (closedLiftGeneratorAugmentation A z M).hom ≫ f =
      (closedLiftGeneratorAugmentation A z M).hom ≫ g)
    (W : X.ProEt) (ha : IsAffine W.left)
    (hw : ∀ (P Q : Sheaf (ProEt.topology X) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op W)))
    (hs : ∀ x : W.left, ∃ y : ↥(pullback W.hom z),
      Specializes x ((pullback.fst W.hom z) y)) (x : M.obj.obj (op W)) :
    f.hom.app (op W) x = g.hom.app (op W) x := by
  let a := (ProEtale.freeSheafHomEquiv (ULift.{u + 1, u} A) W M).symm x
  let F := ProEtale.freeSheaf (ULift.{u + 1, u} A) X
  let J := { t : Σ W : X.ProEt, F.obj W ⟶ M //
    IsAffine t.1.left ∧
      (∀ (P Q : Sheaf (ProEt.topology X) (Type (u + 1))) (φ : P ⟶ Q),
        Epi φ → Function.Surjective (φ.hom.app (op t.1))) ∧
      (∀ x : t.1.left, ∃ y : ↥(pullback t.1.hom z),
        Specializes x ((pullback.fst t.1.hom z) y)) }
  have hfg : a ≫ f = a ≫ g := by
    have H := congrArg
      (fun k ↦ Sigma.ι (fun t : J ↦ F.obj t.val.1) ⟨⟨W, a⟩, ha, hw, hs⟩ ≫ k) h
    simpa only [closedLiftGeneratorAugmentation, Arrow.mk_hom, Category.assoc,
      Sigma.ι_comp_desc_assoc] using H
  have H := congrArg (ProEtale.freeSheafHomEquiv (ULift.{u + 1, u} A) W N) hfg
  simpa only [ProEtale.freeSheafHomEquiv_comp, a, Equiv.apply_symm_apply] using H

private theorem augmentation_cancel_directImage
    (A : Type u) [CommRing A] {X Z U : Scheme.{u}}
    (z : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion z] [IsOpenImmersion j]
    [QuasiCompact j] (hpair : Set.range j = (Set.range z)ᶜ)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (N : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (f g : M ⟶ (ProEtale.lowerStar _ z).obj N)
    (h : (closedLiftGeneratorAugmentation A z M).hom ≫ f =
      (closedLiftGeneratorAugmentation A z M).hom ≫ g) : f = g := by
  apply (sheafToPresheaf _ _).map_injective
  ext T x
  let P := (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) z).obj N
  let P' := (sheafCompose (ProEt.topology X)
    (CategoryTheory.forget (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))).obj P
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).mp P'.property
  let O := ProEt.mk j
  let : IsOpenImmersion O.hom := ‹IsOpenImmersion j›
  let : QuasiCompact O.hom := ‹QuasiCompact j›
  obtain ⟨I, V, v, hv, hV⟩ := localization_cover z O hpair T.unop
  apply (hsh.isSheafFor_of_mem_precoverage hv).isSeparatedFor.ext
  rintro W a ⟨i⟩
  change P.obj.map (v i).op (f.hom.app T x) = P.obj.map (v i).op (g.hom.app T x)
  rcases hV i with ho | ⟨ha, hw, hs⟩
  · obtain ⟨φ⟩ := ho
    have he : IsEmpty ↥(pullback (V i).hom z) := by
      apply Scheme.isEmpty_pullback
      apply Set.disjoint_left.mpr
      rintro y ⟨w, rfl⟩ hy
      have hm : (V i).hom w ∈ Set.range j :=
        ⟨φ.left w, congrArg (fun k : (V i).left ⟶ X ↦ k w)
          (MorphismProperty.Over.w φ)⟩
      rw [hpair] at hm
      exact hm hy
    let Q := (sheafCompose (ProEt.topology Z)
      (CategoryTheory.forget (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))).obj N
    let : IsEmpty ((proEtaleBaseChange z).obj (V i)).left := he
    have : Subsingleton (Q.obj.obj (op ((proEtaleBaseChange z).obj (V i)))) :=
      (Types.isTerminalEquivUnique _
        (Q.isTerminalOfBotCover _ (ProEt.bot_mem_topology _))).instSubsingleton
    exact @Subsingleton.elim
      (Q.obj.obj (op ((proEtaleBaseChange z).obj (V i)))) this _ _
  · have hf := ConcreteCategory.congr_hom (f.hom.naturality (v i).op) x
    have hg := ConcreteCategory.congr_hom (g.hom.naturality (v i).op) x
    exact hf.symm.trans ((augmentation_tests A z M P f g h (V i) ha hw hs _).trans hg)

/-- The augmentation covers after closed inverse image, and closed inverse image
is fully faithful on maps out of its source. -/
theorem closedLiftGeneratorPresentation
    (A : Type u) [CommRing A] {X Z U : Scheme.{u}}
    (z : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion z] [IsOpenImmersion j]
    [QuasiCompact j] (hpair : Set.range j = (Set.range z)ᶜ)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    let L := ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) z
    let e := closedLiftGeneratorAugmentation A z M
    Epi (L.map e.hom) ∧
      ∀ N : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)),
        Function.Bijective (fun f : e.left ⟶ N ↦ L.map f)  := by
  dsimp
  constructor
  · constructor
    intro N f g h
    let a := ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) z
    apply (a.homEquiv _ _).injective
    apply augmentation_cancel_directImage A z j hpair M N
    simpa only [← a.homEquiv_naturality_left] using congrArg (a.homEquiv _ _) h
  · intro N
    classical
    let Λ := ULift.{u + 1, u} A
    let F := ProEtale.freeSheaf Λ X
    let a := ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) z
    let J := { t : Σ W : X.ProEt, F.obj W ⟶ M //
      IsAffine t.1.left ∧
        (∀ (P Q : Sheaf (ProEt.topology X) (Type (u + 1))) (φ : P ⟶ Q),
          Epi φ → Function.Surjective (φ.hom.app (op t.1))) ∧
        (∀ x : t.1.left, ∃ y : ↥(pullback t.1.hom z),
          Specializes x ((pullback.fst t.1.hom z) y)) }
    have hlocal (t : J) : Function.Bijective
        (fun f : F.obj t.val.1 ⟶ N ↦ f ≫ a.unit.app N) := by
      let : IsAffine t.val.1.left := t.property.1
      have hu := module_unit_bijective Λ z t.val.1 t.property.2.1 t.property.2.2 N
      change Function.Bijective ((a.unit.app N).hom.app (op t.val.1)) at hu
      constructor
      · intro f g h
        apply (ProEtale.freeSheafHomEquiv Λ t.val.1 N).injective
        apply hu.1
        have hh := congrArg (ProEtale.freeSheafHomEquiv Λ t.val.1
          ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) z).obj
            ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) z).obj N))) h
        rw [ProEtale.freeSheafHomEquiv_comp,
          ProEtale.freeSheafHomEquiv_comp] at hh
        exact hh
      · intro f
        obtain ⟨x, hx⟩ := hu.2 (ProEtale.freeSheafHomEquiv Λ t.val.1 _ f)
        refine ⟨(ProEtale.freeSheafHomEquiv Λ t.val.1 N).symm x, ?_⟩
        apply (ProEtale.freeSheafHomEquiv Λ t.val.1 _).injective
        rw [ProEtale.freeSheafHomEquiv_comp, Equiv.apply_symm_apply]
        exact hx
    have hsum : Function.Bijective
        (fun f : (∐ fun t : J ↦ F.obj t.val.1) ⟶ N ↦ f ≫ a.unit.app N) := by
      constructor
      · intro f g h
        apply Sigma.hom_ext
        intro t
        apply (hlocal t).1
        simpa only [Category.assoc] using
          congrArg (fun k ↦ Sigma.ι (fun t : J ↦ F.obj t.val.1) t ≫ k) h
      · intro f
        choose g hg using fun t : J ↦ (hlocal t).2 (Sigma.ι (fun t : J ↦ F.obj t.val.1) t ≫ f)
        refine ⟨Sigma.desc g, ?_⟩
        apply Sigma.hom_ext
        intro t
        simpa only [Sigma.ι_comp_desc_assoc] using hg t
    have hs : Function.Bijective
        (fun f : (closedLiftGeneratorAugmentation A z M).left ⟶ N ↦ f ≫ a.unit.app N) :=
      hsum
    convert (a.homEquiv _ _).symm.bijective.comp hs using 1
    funext f
    change (ProEtale.upperStar (ModuleCat.{u + 1} Λ) z).map f =
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ) z).map (f ≫ a.unit.app N) ≫
        a.counit.app _
    rw [Functor.map_comp, Category.assoc, a.left_triangle_components, Category.comp_id]

end AlgebraicGeometry.Scheme
