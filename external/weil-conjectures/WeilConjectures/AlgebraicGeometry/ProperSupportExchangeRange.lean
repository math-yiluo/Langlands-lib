/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
public import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility

/-! # The image of the ordinary exchange on proper-support sections

Source: Stacks Project, Tags 0F55 and 0F76
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

private theorem properSupportInclusion_mono
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Mono ((properSupportLowerStarInclusion Λ f).app F) := by
  have h (V : Y.Etaleᵒᵖ) :
      Mono (((properSupportLowerStarInclusion Λ f).app F).hom.app V) :=
    (ModuleCat.mono_iff_injective _).2
      (properSupportLowerStarInclusion_range Λ f F V.unop).1
  have : Mono ((properSupportLowerStarInclusion Λ f).app F).hom :=
    NatTrans.mono_of_mono_app ((properSupportLowerStarInclusion Λ f).app F).hom
  exact Sheaf.Hom.mono_of_presheaf_mono Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    ((properSupportLowerStarInclusion Λ f).app F)

private theorem properSupportUnitPullback_eq_square
    (Λ : Type (u + 1)) [CommRing Λ] {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : IsPullback a f' f b)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : Y.Etale) :
    properSupportUnitPullback a f b f' sq F U =
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).unit.app F).hom.app
        (op (f.Etale.obj U)) ≫
        ((squareLowerStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app
          ((upperStar (ModuleCat.{u + 1} Λ) a).obj F)).hom.app (op U) := by
  unfold properSupportUnitPullback squareLowerStarIso
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, lowerStarComp,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
    Functor.sheafPushforwardContinuousComp'_inv_app_hom_app,
    Iso.symm_inv, ← Functor.map_comp, ← op_comp]
  congr 2
  apply congrArg Quiver.Hom.op
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [properSupportBaseChangeEtaleMap, properSupportBaseChangeProjection,
        MorphismProperty.Over.homMk_hom, Over.homMk_left,
        MorphismProperty.Comma.comp_hom, Comma.comp_left,
        MorphismProperty.Over.pullbackComp_hom_app_left,
        MorphismProperty.Over.pullbackComp_inv_app_left, Category.assoc,
        pullback.lift_fst]
      erw [pullbackLeftPullbackSndIso_inv_fst]
      simp only [pullback.map, pullback.lift_fst, Category.comp_id,
        pullbackLeftPullbackSndIso_hom_fst]
      erw [pullback.lift_fst]
      rfl
    · simp only [properSupportBaseChangeEtaleMap, properSupportBaseChangeProjection,
        MorphismProperty.Over.homMk_hom, Over.homMk_left,
        MorphismProperty.Comma.comp_hom, Comma.comp_left,
        MorphismProperty.Over.pullbackComp_hom_app_left,
        MorphismProperty.Over.pullbackComp_inv_app_left, Category.assoc,
        pullback.lift_fst_assoc]
      erw [pullbackLeftPullbackSndIso_inv_fst_snd]
      simp only [pullback.map, Category.assoc, pullback.lift_snd_assoc,
        Category.id_comp, pullbackLeftPullbackSndIso_hom_snd_assoc]
      erw [pullback.lift_snd]
      rfl
  · simp only [properSupportBaseChangeEtaleMap,
      MorphismProperty.Over.homMk_hom, Over.homMk_left,
      MorphismProperty.Comma.comp_hom, Comma.comp_left,
      MorphismProperty.Over.pullbackComp_hom_app_left,
      MorphismProperty.Over.pullbackComp_inv_app_left, Category.assoc, pullback.lift_snd]
    erw [pullbackLeftPullbackSndIso_inv_snd_snd]
    simp only [pullback.map, pullback.lift_snd, Category.comp_id,
      pullbackLeftPullbackSndIso_hom_snd]
    rfl

/-- The ordinary exchange, restricted to the inverse image of the proper-support
subsheaf, is injective and has exactly the proper-support sections as image.

Source: Stacks Project, Tags 0F55 and 0F76.
(auxiliary; not a blueprint node)

Proof:
Pullback of a section pulls its support back, so properness survives base change.
This defines a map G -> b_*H, for G = f_! F and H = f'_! a^*F. Adjunction gives
beta : b^*G -> H. Naturality of the adjunction identifies its composite with H's
inclusion with the restricted ordinary comparison. At an algebraically closed
geometric point, properSupport_geometricStalk identifies both support stalks with
properly supported sections on the same geometric fibre. Inverse-image stalk/germ
compatibility and the Cartesian fibre identification identify beta with the identity
on these sections. It is thus a stalk isomorphism. These geometric points cover the
base, so stalk detection makes beta an isomorphism of sheaves of modules. Composing
this isomorphism with the literal support inclusion gives the stated injectivity and
image equality on every etale object. -/
theorem properSupportExchange_range (Λ : Type (u + 1)) [CommRing Λ]
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (a : X' ⟶ X)
    (b : Y' ⟶ Y) (f' : X' ⟶ Y') [IsSeparated f] [LocallyOfFiniteType f]
    [IsSeparated f'] [LocallyOfFiniteType f'] (sq : IsPullback a f' f b)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y'.Etale) :
    Function.Injective
      (((upperStar (ModuleCat.{u + 1} Λ) b).map
          ((properSupportLowerStarInclusion Λ f).app F) ≫
        (baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F).hom.app (op V)) ∧
    ∀ s, (∃ t,
      (((upperStar (ModuleCat.{u + 1} Λ) b).map
          ((properSupportLowerStarInclusion Λ f).app F) ≫
        (baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F).hom.app (op V)) t = s) ↔
      SectionHasProperSupport Λ ((upperStar (ModuleCat.{u + 1} Λ) a).obj F)
        (f'.Etale.obj V) (pullback.fst V.hom f') s := by
  let A := ModuleCat.{u + 1} Λ
  let G := (properSupportLowerStar Λ f).obj F
  let H := (properSupportLowerStar Λ f').obj ((upperStar A a).obj F)
  let ιG := (properSupportLowerStarInclusion Λ f).app F
  let ιH := (properSupportLowerStarInclusion Λ f').app ((upperStar A a).obj F)
  have : Mono ιG := properSupportInclusion_mono Λ f F
  have : Mono ιH := properSupportInclusion_mono Λ f' ((upperStar A a).obj F)
  have hG := fun U ↦ (properSupportLowerStarInclusion_range Λ f F U).2
  have hH := fun V ↦
    (properSupportLowerStarInclusion_range Λ f' ((upperStar A a).obj F) V).2
  obtain ⟨α, hα, _⟩ := properSupportPullbackSectionMap a f b f' sq F G H ιG ιH hG hH
  let β := ((upperStarLowerStarAdjunction A b).homEquiv G H).symm α
  have hβstalk {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
      (y' : Spec (.of Ω) ⟶ Y') :
      IsIso ((Scheme.pointSmallEtale y').sheafFiber.map β) := by
    obtain ⟨qG, qH, SG, SH, eG, eH, κ₀, κ, _, _, _, _, _, _, he⟩ :=
      properSupport_fibre_restriction_compatibility a f b f' sq F G H ιG ιH
        hG hH α hα y'
    change (Scheme.pointSmallEtale y').sheafFiber.map β ≫ eH.hom ≫ κ.hom = _ at he
    have hh : (Scheme.pointSmallEtale y').sheafFiber.map β =
        ((upperStarCompSheafFiberIso A b y').app G).hom ≫ eG.hom ≫
          κ.inv ≫ eH.inv := by
      rw [← Category.assoc, ← Category.assoc, ← he]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hh]
    infer_instance
  have : IsIso β := by
    apply Scheme.isIso_of_isIso_sheafFiber_map
    intro y
    have := hβstalk (Y'.algClosurePoint y)
    let e := GrothendieckTopology.Point.uliftSheafFiberIso.{u + 1}
      (Scheme.pointSmallEtale (Y'.algClosurePoint y)) A
    dsimp only [Scheme.uliftPointSmallEtale]
    have he := e.hom.naturality β
    have hh : (Scheme.pointSmallEtale (Y'.algClosurePoint y)).ulift.sheafFiber.map β =
        (e.app ((upperStar A b).obj G)).hom ≫
          (Scheme.pointSmallEtale (Y'.algClosurePoint y)).sheafFiber.map β ≫
          (e.app H).inv := by
      change _ = (e.hom.app _ ≫ _) ≫ e.inv.app H
      rw [← he]
      simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    rw [hh]
    infer_instance
  have hcomp : β ≫ ιH =
      (upperStar A b).map ιG ≫ (baseChangeMap A sq.toCommSq).app F := by
    apply ((upperStarLowerStarAdjunction A b).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_unit,
      unit_map_baseChangeMap_app]
    ext U s
    let U := U.unop
    change ιH.hom.app (op (b.Etale.obj U)) (α.hom.app (op U) s) = _
    exact (hα U s).trans
      (ConcreteCategory.congr_hom
        (properSupportUnitPullback_eq_square Λ a f b f' sq F U)
        (ιG.hom.app (op U) s))
  have hβV : Function.Bijective (β.hom.app (op V)) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have hιV := properSupportLowerStarInclusion_range Λ f' ((upperStar A a).obj F) V
  have heq := congrArg (fun φ ↦ φ.hom.app (op V)) hcomp
  rw [← heq]
  change Function.Injective (ιH.hom.app (op V) ∘ β.hom.app (op V)) ∧ _
  refine ⟨hιV.1.comp hβV.1, ?_⟩
  intro s
  rw [← hιV.2 s]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨β.hom.app (op V) t, ht⟩
  · rintro ⟨t, ht⟩
    obtain ⟨r, rfl⟩ := hβV.2 t
    exact ⟨r, ht⟩

end AlgebraicGeometry.Etale
