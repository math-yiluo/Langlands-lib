/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
import WeilConjectures.AlgebraicGeometry.ProperGeometricPointExchange
import WeilConjectures.AlgebraicGeometry.ProperSupportCompositeRange
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import WeilConjectures.SixFunctors.OpenClosed.Exact

/-! The geometric part of the proper-support stalk image calculation. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_unit_germ
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y.Etale)
    (v : (pointSmallEtale (x ≫ f)).fiber.obj V) :
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F).hom.app
          (op V) ≫
        (pointSmallEtale x).toPresheafFiber (f.Etale.obj V)
          ((pointSmallEtaleFiberEtaleIso f x).inv.app V v)
          ((upperStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫
        (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) f x).hom.app F =
      (pointSmallEtale (x ≫ f)).toPresheafFiber V v F.obj := by
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv
    ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) f x).app F)).1
  simp only [upperStarCompSheafFiberIso, Iso.app_inv, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_assoc]
  rw [show (pointSmallEtale x).sheafFiber.map _ =
    (pointSmallEtale x).presheafFiber.map _ from rfl,
    GrothendieckTopology.Point.toPresheafFiber_naturality]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ f) (ModuleCat.{u + 1} Λ)
      (Y.smallGrothendieckTopology (P := @Etale))
      (X.smallGrothendieckTopology (P := @Etale)))
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f) F
  have huV := NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (op V)
  rw [← Category.assoc, ← huV]
  rfl

private theorem germ_zero_change_point
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale)
    (s : F.obj.obj (op V)) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (p q : Spec (.of Ω) ⟶ X) (hpq : p = q) (v : Spec (.of Ω) ⟶ V.left)
    (hv : v ≫ V.hom = p) (hv' : v ≫ V.hom = q) :
    (pointSmallEtale p).toPresheafFiber V (Over.homMk v hv) F.obj s = 0 ↔
      (pointSmallEtale q).toPresheafFiber V (Over.homMk v hv') F.obj s = 0 := by
  cases hpq
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_restrict_germ_zero
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y.Etale)
    (W : X.Etale) (h : W ⟶ f.Etale.obj V) (s : F.obj.obj (op V))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (k : Spec (.of Ω) ⟶ W.left) :
    (pointSmallEtale (k ≫ W.hom)).toPresheafFiber W (Over.homMk k)
        ((upperStar (ModuleCat.{u + 1} Λ) f).obj F).obj
        (((upperStar (ModuleCat.{u + 1} Λ) f).obj F).obj.map h.op
          (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F).hom.app
            (op V) s)) = 0 ↔
      (pointSmallEtale (((k ≫ h.left) ≫ pullback.fst V.hom f) ≫ V.hom)).toPresheafFiber V
        (Over.homMk ((k ≫ h.left) ≫ pullback.fst V.hom f)) F.obj s = 0 := by
  let x := k ≫ W.hom
  let b := (k ≫ h.left) ≫ pullback.fst V.hom f
  have hb : b ≫ V.hom = x ≫ f := by
    dsimp only [b, x]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun a ↦ (k ≫ a) ≫ f) h.w
  let v : (pointSmallEtale (x ≫ f)).fiber.obj V := Over.homMk b hb
  let w : (pointSmallEtale x).fiber.obj W := Over.homMk k rfl
  have hw : (pointSmallEtale x).fiber.map h w =
      (pointSmallEtaleFiberEtaleIso f x).inv.app V v := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact (pointSmallEtaleFiberEtaleIso_inv_app_left_fst f x V v).symm
    · exact (Over.Hom.w ((pointSmallEtale x).fiber.map h w)).trans
        (Over.Hom.w ((pointSmallEtaleFiberEtaleIso f x).inv.app V v)).symm
  let H := (upperStar (ModuleCat.{u + 1} Λ) f).obj F
  let a := ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F).hom.app
    (op V) s
  have hg := (pointSmallEtale x).toPresheafFiber_w_apply h w H.obj a
  rw [hw] at hg
  have hu := ConcreteCategory.congr_hom (pullback_unit_germ Λ f x F V v) s
  change ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) f x).hom.app F)
    ((pointSmallEtale x).toPresheafFiber (f.Etale.obj V)
      ((pointSmallEtaleFiberEtaleIso f x).inv.app V v) H.obj a) =
    (pointSmallEtale (x ≫ f)).toPresheafFiber V v F.obj s at hu
  have hinj := (ConcreteCategory.isIso_iff_bijective
    ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) f x).hom.app F)).1
      (by infer_instance) |>.1
  change (pointSmallEtale x).toPresheafFiber W w H.obj (H.obj.map h.op a) = 0 ↔ _
  rw [hg]
  suffices hh : (pointSmallEtale x).toPresheafFiber (f.Etale.obj V)
      ((pointSmallEtaleFiberEtaleIso f x).inv.app V v) H.obj a = 0 ↔
      (pointSmallEtale (x ≫ f)).toPresheafFiber V v F.obj s = 0 by
    exact hh.trans (germ_zero_change_point Λ F V s (x ≫ f)
      (b ≫ V.hom) hb.symm b hb rfl)
  constructor
  · intro hz
    rw [← hu, hz, map_zero]
  · intro hz
    apply hinj
    rw [map_zero, hu, hz]

set_option backward.isDefEq.respectTransparency false in
private theorem closed_support_pullback
    {T S T' S' : Scheme.{u}} (p : T ⟶ S) [LocallyOfFiniteType p]
    (a : T' ⟶ T) (q : T' ⟶ S') [LocallyOfFiniteType q] (b : S' ⟶ S)
    (sq : IsPullback a q p b) (C : TopologicalSpace.Closeds T)
    (hp : IsClosedSubsetProperOver p C) :
    IsClosedSubsetProperOver q (C.preimage a.continuous) := by
  let i := (IdealSheafData.vanishingIdeal C).subschemeι
  have hi : Set.range i = (C : Set T) := by simp [i]
  have hsq := (IsPullback.of_hasPullback i a).paste_vert sq
  have : IsProper (i ≫ p) := hp
  have hproper : IsProper (pullback.snd i a ≫ q) :=
    MorphismProperty.of_isPullback hsq inferInstance
  apply (closed_subset_proper_over_base_properties q
    (C.preimage a.continuous)).1.mpr
  refine ⟨_, pullback.snd i a, inferInstance, ?_, hproper⟩
  change Set.range (pullback.snd i a) = a ⁻¹' (C : Set T)
  rw [Scheme.Pullback.range_snd, hi]

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_restrict_properSupport
    (Λ : Type (u + 1)) [CommRing Λ] {X Y S S' : Scheme.{u}} (g : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y.Etale)
    (W : X.Etale) (h : W ⟶ g.Etale.obj V) (s : F.obj.obj (op V))
    (p : V.left ⟶ S) [LocallyOfFiniteType p]
    (q : W.left ⟶ S') [LocallyOfFiniteType q] (b : S' ⟶ S)
    (sq : IsPullback (h.left ≫ pullback.fst V.hom g) q p b)
    (hs : SectionHasProperSupport Λ F V p s) :
    SectionHasProperSupport Λ ((upperStar (ModuleCat.{u + 1} Λ) g).obj F) W q
      (((upperStar (ModuleCat.{u + 1} Λ) g).obj F).obj.map h.op
        (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app F).hom.app
          (op V) s)) := by
  obtain ⟨T, hT, hp⟩ := (sectionHasProperSupport_iff Λ F V p s).1 hs
  apply (sectionHasProperSupport_iff Λ _ W q _).2
  refine ⟨T.preimage (h.left ≫ pullback.fst V.hom g).continuous, ?_,
    closed_support_pullback p _ q b sq T hp⟩
  intro Ω _ _ k
  change (h.left ≫ pullback.fst V.hom g) (k default) ∈ T ↔ _
  have ht := hT Ω ((k ≫ h.left) ≫ pullback.fst V.hom g)
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at ht
  exact ht.trans (not_congr (pullback_restrict_germ_zero Λ g F V W h s k)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem fibre_restriction_properSupport
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V)
    (s : F.obj.obj (op (f.Etale.obj V)))
    (hs : SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) s) :
    SectionHasProperSupport Λ
      ((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f y)).obj F)
      (Scheme.Etale.mk (𝟙 (pullback f y))) (pullback.snd f y)
      (geometricFibreSectionRestriction Λ (IsPullback.of_hasPullback f y).toCommSq
        F V v s) := by
  let g := pullback.fst f y
  let q := pullback.snd f y
  let W := Scheme.Etale.mk (𝟙 (pullback f y))
  let h := geometricFibreSectionLift (IsPullback.of_hasPullback f y).toCommSq V v
  let a := h.left ≫ pullback.fst (f.Etale.obj V).hom g
  have ha : a ≫ pullback.fst V.hom f = q ≫ v.left := by
    simp [a, h, g, q, geometricFibreSectionLift]
  have hag : a ≫ (f.Etale.obj V).hom = g := by
    change a ≫ pullback.snd V.hom f = g
    simp [a, h, g, geometricFibreSectionLift]
  have hv : v.left ≫ V.hom = y := v.w
  have sq : IsPullback a q (pullback.fst V.hom f) v.left := by
    apply IsPullback.of_right (h₁₂ := (f.Etale.obj V).hom) (v₁₃ := f) ?_ ha
      (IsPullback.of_hasPullback V.hom f).flip
    rw [hag, hv]
    exact IsPullback.of_hasPullback f y
  exact pullback_restrict_properSupport Λ g F (f.Etale.obj V) W h s
    (pullback.fst V.hom f) q v.left sq hs

set_option backward.isDefEq.respectTransparency false in
private theorem properSupport_stalk_range_subset
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (i : G ⟶ (lowerStar (ModuleCat.{u + 1} Λ) f).obj F)
    (hG : ∀ (V : Y.Etale) (s : F.obj.obj (op (f.Etale.obj V))),
      (∃ t, i.hom.app (op V) t = s) ↔
        SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) s)
    (c : lowerStar (ModuleCat.{u + 1} Λ) f ⋙ (pointSmallEtale y).sheafFiber ⟶
      upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f y) ⋙
        (sheafSections (pullback f y).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (op (Scheme.Etale.mk (𝟙 (pullback f y)))))
    (hc : ∀ (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V)
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (pointSmallEtale y).toPresheafFiber V v
          ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ c.app F =
        geometricFibreSectionRestriction Λ (IsPullback.of_hasPullback f y).toCommSq F V v)
    (s : ((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G) :
    SectionHasProperSupport Λ
      ((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f y)).obj F)
      (Scheme.Etale.mk (𝟙 (pullback f y))) (pullback.snd f y)
      (((pointSmallEtale y).sheafFiber.map i ≫ c.app F) s) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨V, v, t, rfl⟩ :=
    (pointSmallEtale y).toPresheafFiber_jointly_surjective (P := G.obj) s
  have hnat := (pointSmallEtale y).toPresheafFiber_naturality_apply i.hom V v t
  change (pointSmallEtale y).sheafFiber.map i
    ((pointSmallEtale y).toPresheafFiber V v G.obj t) =
      (pointSmallEtale y).toPresheafFiber V v
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj (i.hom.app (op V) t) at hnat
  have he := ConcreteCategory.congr_hom (hc V v F) (i.hom.app (op V) t)
  change (c.app F)
    ((pointSmallEtale y).toPresheafFiber V v
      ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj (i.hom.app (op V) t)) = _ at he
  change SectionHasProperSupport Λ _ _ _ ((c.app F)
    ((pointSmallEtale y).sheafFiber.map i
      ((pointSmallEtale y).toPresheafFiber V v G.obj t)))
  rw [hnat, he]
  exact fibre_restriction_properSupport Λ f y F V v (i.hom.app (op V) t)
    ((hG V _).1 ⟨t, rfl⟩)

set_option backward.isDefEq.respectTransparency false in
private theorem properSupport_restriction_kernel
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V)
    (s : F.obj.obj (op (f.Etale.obj V)))
    (hs : SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) s)
    (hz : geometricFibreSectionRestriction Λ (IsPullback.of_hasPullback f y).toCommSq
      F V v s = 0) :
    (pointSmallEtale y).toPresheafFiber V v
      ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj s = 0 := by
  classical
  let P := (properSupportLowerStar Λ f).obj F
  let t : P.obj.obj (op V) := ⟨s, hs⟩
  obtain ⟨T, I, hT, _, hI, hIg⟩ := properSupportSectionImage Λ f F V t
  let g := pullback.fst f y
  let q := pullback.snd f y
  let W := Scheme.Etale.mk (𝟙 (pullback f y))
  let h := geometricFibreSectionLift (IsPullback.of_hasPullback f y).toCommSq V v
  let a := h.left ≫ pullback.fst (f.Etale.obj V).hom g
  have ha : a ≫ pullback.fst V.hom f = q ≫ v.left := by
    simp [a, h, g, q, geometricFibreSectionLift]
  have hag : a ≫ (f.Etale.obj V).hom = g := by
    change a ≫ pullback.snd V.hom f = g
    simp [a, h, g, geometricFibreSectionLift]
  have sq : IsPullback a q (pullback.fst V.hom f) v.left := by
    apply IsPullback.of_right (h₁₂ := (f.Etale.obj V).hom) (v₁₃ := f) ?_ ha
      (IsPullback.of_hasPullback V.hom f).flip
    have hv : v.left ≫ V.hom = y := v.w
    rw [hag, hv]
    exact IsPullback.of_hasPullback f y
  have hn : v.left (default : Spec (.of Ω)) ∉ I := by
    intro hv
    change v.left (default : Spec (.of Ω)) ∈ (I : Set V.left) at hv
    rw [hI] at hv
    obtain ⟨x, hxT, hx⟩ := hv
    have hxa : x ∈ Set.range a := by
      rw [Scheme.range_snd_of_isPullback sq.flip]
      exact ⟨default, hx.symm⟩
    obtain ⟨z, rfl⟩ := hxa
    let K := AlgebraicClosure ((pullback f y).residueField z)
    let k : Spec (.of K) ⟶ pullback f y := (pullback f y).algClosurePoint z
    have hk : k default = z := Scheme.algClosurePoint_base _ _ _
    have ht := hT K ((k ≫ h.left) ≫ pullback.fst (f.Etale.obj V).hom g)
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hk] at ht
    have hg := (pullback_restrict_germ_zero Λ g F (f.Etale.obj V) W h s k).1
      (by
        change (pointSmallEtale (k ≫ W.hom)).toPresheafFiber W (Over.homMk k)
          ((upperStar (ModuleCat.{u + 1} Λ) g).obj F).obj
          (geometricFibreSectionRestriction Λ
            (IsPullback.of_hasPullback f y).toCommSq F V v s) = 0
        rw [hz, map_zero])
    exact (ht.1 hxT) hg
  have hzP : (pointSmallEtale (v.left ≫ V.hom)).toPresheafFiber V
      (Over.homMk v.left) P.obj t = 0 := by
    by_contra hh
    exact hn ((hIg Ω v.left).2 hh)
  have hzP' : (pointSmallEtale y).toPresheafFiber V v P.obj t = 0 := by
    obtain ⟨v', hv', rfl⟩ := Over.homMk_surjective v
    exact (germ_zero_change_point Λ P V t (v' ≫ V.hom) y hv' v' rfl hv').1 hzP
  let j := (properSupportLowerStarInclusion Λ f).app F
  have he := (pointSmallEtale y).toPresheafFiber_naturality_apply j.hom V v t
  rw [hzP', map_zero] at he
  exact he.symm

set_option backward.isDefEq.respectTransparency false in
private theorem properSupport_stalk_injective
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (i : G ⟶ (lowerStar (ModuleCat.{u + 1} Λ) f).obj F)
    (hi : Mono i)
    (hG : ∀ (V : Y.Etale) (s : F.obj.obj (op (f.Etale.obj V))),
      (∃ t, i.hom.app (op V) t = s) ↔
        SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) s)
    (c : lowerStar (ModuleCat.{u + 1} Λ) f ⋙ (pointSmallEtale y).sheafFiber ⟶
      upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f y) ⋙
        (sheafSections (pullback f y).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (op (Scheme.Etale.mk (𝟙 (pullback f y)))))
    (hc : ∀ (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V)
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (pointSmallEtale y).toPresheafFiber V v
          ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ c.app F =
        geometricFibreSectionRestriction Λ (IsPullback.of_hasPullback f y).toCommSq F V v)
    : Function.Injective (((pointSmallEtale y).sheafFiber.map i ≫ c.app F).hom) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : Mono i := hi
  have : AB5OfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1} (ModuleCat.{u + 1} Λ)
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} (ModuleCat.{u + 1} Λ)
  apply (injective_iff_map_eq_zero _).2
  intro s hs
  have hinj := (ModuleCat.mono_iff_injective ((pointSmallEtale y).sheafFiber.map i)).1
    (by infer_instance)
  apply hinj
  rw [map_zero]
  obtain ⟨V, v, t, rfl⟩ :=
    (pointSmallEtale y).toPresheafFiber_jointly_surjective (P := G.obj) s
  have hnat := (pointSmallEtale y).toPresheafFiber_naturality_apply i.hom V v t
  change (pointSmallEtale y).sheafFiber.map i
    ((pointSmallEtale y).toPresheafFiber V v G.obj t) =
      (pointSmallEtale y).toPresheafFiber V v
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj (i.hom.app (op V) t) at hnat
  rw [hnat]
  apply properSupport_restriction_kernel Λ f y F V v (i.hom.app (op V) t)
    ((hG V _).1 ⟨t, rfl⟩)
  have he := ConcreteCategory.congr_hom (hc V v F) (i.hom.app (op V) t)
  change (c.app F) ((pointSmallEtale y).toPresheafFiber V v
    ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj (i.hom.app (op V) t)) = _ at he
  rw [← hnat] at he
  exact he.symm.trans hs

set_option backward.isDefEq.respectTransparency false in
private theorem section_support_iso_iff
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {V W : X.Etale}
    (e : V ≅ W) (p : V.left ⟶ S) (q : W.left ⟶ S)
    [LocallyOfFiniteType p] [LocallyOfFiniteType q] [IsSeparated p] [IsSeparated q]
    (he : e.hom.left ≫ q = p) (s : F.obj.obj (op W)) :
    SectionHasProperSupport Λ F V p (F.obj.map e.hom.op s) ↔
      SectionHasProperSupport Λ F W q s := by
  have forward {V W : X.Etale} (e : V ≅ W) (p : V.left ⟶ S) (q : W.left ⟶ S)
      [LocallyOfFiniteType p] [LocallyOfFiniteType q] [IsSeparated q]
      (he : e.hom.left ≫ q = p) (s : F.obj.obj (op W))
      (hs : SectionHasProperSupport Λ F V p (F.obj.map e.hom.op s)) :
      SectionHasProperSupport Λ F W q s := by
    obtain ⟨C, hC, hp⟩ := (sectionHasProperSupport_iff Λ F V p _).1 hs
    let ee : V.left ≅ W.left :=
      (MorphismProperty.Over.forget @Etale ⊤ X ⋙ CategoryTheory.Over.forget X).mapIso e
    apply (sectionHasProperSupport_iff Λ F W q s).2
    refine ⟨C.preimage ee.inv.continuous, ?_, proper_iso_image p q ee he C hp⟩
    intro Ω _ _ v
    have hg := not_congr (etaleModuleGerm_restrict_zero Λ F e.hom s Ω (v ≫ ee.inv))
    have hv : (v ≫ ee.inv) ≫ e.hom.left = v := by
      change (v ≫ ee.inv) ≫ ee.hom = v
      simp
    have hc := hC Ω (v ≫ ee.inv)
    rw [Scheme.Hom.comp_apply] at hc
    change ee.inv (v default) ∈ C ↔ _
    apply hc.trans
    apply hg.trans
    exact iff_of_eq (congrArg (fun w : Spec (.of Ω) ⟶ W.left =>
      (Scheme.pointSmallEtale (w ≫ W.hom)).toPresheafFiber W (Over.homMk w) F.obj s ≠ 0) hv)
  constructor
  · exact forward e p q he s
  · intro hs
    have he' : e.inv.left ≫ p = q := by
      rw [← he]
      have hi : e.inv.left ≫ e.hom.left = 𝟙 _ := by
        exact congrArg (fun h => h.left) e.inv_hom_id
      rw [← Category.assoc, hi, Category.id_comp]
    have h := forward e.symm q p he' (F.obj.map e.hom.op s) ?_
    · exact h
    · have hmap : F.obj.map e.inv.op (F.obj.map e.hom.op s) = s := by
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        simp
      change SectionHasProperSupport Λ F W q
        (F.obj.map e.inv.op (F.obj.map e.hom.op s))
      rwa [hmap]

set_option backward.isDefEq.respectTransparency false in
private theorem geometricFibreSectionLift_naturality
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : CommSq g' f' f s)
    {V W : Y.Etale} (a : V ⟶ W) (v : (Scheme.pointSmallEtale s).fiber.obj V) :
    geometricFibreSectionLift sq V v ≫ g'.Etale.map (f.Etale.map a) =
      geometricFibreSectionLift sq W ((Scheme.pointSmallEtale s).fiber.map a v) := by
  apply MorphismProperty.Over.Hom.ext
  change (geometricFibreSectionLift sq V v).left ≫
    (g'.Etale.map (f.Etale.map a)).left = _
  dsimp [geometricFibreSectionLift, Hom.Etale, MorphismProperty.Over.pullback,
    Scheme.pointSmallEtale]
  apply Limits.pullback.hom_ext
  · apply Limits.pullback.hom_ext
    · simp [Category.assoc]
      rfl
    · simp [Category.assoc]
  · simp

set_option backward.isDefEq.respectTransparency false in
private theorem geometricFibreSectionRestriction_naturality
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : CommSq g' f' f s)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {V W : Y.Etale} (a : V ⟶ W) (v : (Scheme.pointSmallEtale s).fiber.obj V) :
    F.obj.map (f.Etale.map a).op ≫ geometricFibreSectionRestriction Λ sq F V v =
      geometricFibreSectionRestriction Λ sq F W ((Scheme.pointSmallEtale s).fiber.map a v) := by
  unfold geometricFibreSectionRestriction
  erw [← Category.assoc,
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g').unit.app F).hom.naturality
      (f.Etale.map a).op]
  change _ ≫ (((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.map
    (g'.Etale.map (f.Etale.map a)).op ≫ _) = _
  rw [← Functor.map_comp, ← op_comp,
    geometricFibreSectionLift_naturality]

set_option backward.isDefEq.respectTransparency false in
private theorem proper_restriction_isIso
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    {X' : Scheme.{u}} {g : X' ⟶ X} {q : X' ⟶ Spec (.of Ω)}
    (sq : IsPullback g q f y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (c : (pointSmallEtale y).sheafFiber.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ⟶
      ((upperStar (ModuleCat.{u + 1} Λ) g).obj F).obj.obj
        (op (Scheme.Etale.mk (𝟙 X'))))
    (hc : ∀ (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V),
      (pointSmallEtale y).toPresheafFiber V v
          ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ c =
        geometricFibreSectionRestriction Λ sq.toCommSq F V v)
    : IsIso c := by
  have hbase := isIso_baseChangeMap_app_of_isProper_geometricPoint Λ sq F
  obtain ⟨b, hb⟩ := geometricFibreExchange_germs Λ sq F c (by
    intro V v s
    exact ConcreteCategory.congr_hom (hc V v) s)
  have hcomp : IsIso
      ((geometricPointSourceStalkIso Λ y ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F)).hom ≫
        c) := by
    rw [← hb]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (geometricPointSourceStalkIso Λ y ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F)).hom _

set_option backward.isDefEq.respectTransparency false in
private theorem proper_fibre_section_lift
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    {X' : Scheme.{u}} {g : X' ⟶ X} {q : X' ⟶ Spec (.of Ω)}
    (sq : IsPullback g q f y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (s : ((upperStar (ModuleCat.{u + 1} Λ) g).obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 X')))) :
    ∃ (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V)
      (t : F.obj.obj (op (f.Etale.obj V))),
      geometricFibreSectionRestriction Λ sq.toCommSq F V v t =
        s := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let c := (pointSmallEtale y).presheafFiberDesc
    (P := ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj)
    (fun V v ↦ geometricFibreSectionRestriction Λ
      sq.toCommSq F V v)
    (fun _ _ a v ↦ geometricFibreSectionRestriction_naturality Λ
      sq.toCommSq F a v)
  have hc (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V) :
      (pointSmallEtale y).toPresheafFiber V v
          ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ c =
        geometricFibreSectionRestriction Λ sq.toCommSq F V v :=
    (pointSmallEtale y).toPresheafFiber_presheafFiberDesc _ _ V v
  have : IsIso c := proper_restriction_isIso Λ f y sq F c hc
  obtain ⟨z, rfl⟩ := (ConcreteCategory.isIso_iff_bijective c).1 inferInstance |>.2 s
  obtain ⟨V, v, t, rfl⟩ := (pointSmallEtale y).toPresheafFiber_jointly_surjective z
  exact ⟨V, v, t, (ConcreteCategory.congr_hom (hc V v) t).symm⟩

set_option backward.isDefEq.respectTransparency false in
private theorem open_extension_section_lift
    (Λ : Type (u + 1)) [CommRing Λ] {X Z S : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ S) [IsSeparated p]
    [LocallyOfFiniteType p] (f : X ⟶ S) [LocallyOfFiniteType f]
    (hf : j ≫ p = f)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (s : F.obj.obj (op (Scheme.Etale.mk (𝟙 X))))
    (hs : SectionHasProperSupport Λ F (Scheme.Etale.mk (𝟙 X)) f s) :
    let V := Scheme.Etale.mk (𝟙 Z)
    let W := Scheme.Etale.mk (𝟙 X)
    let e : j.Etale.obj V ≅ W :=
      ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Z).isTerminalObj
        j.Etale).uniqueUpToIso (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)
    ∃ t : ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj F).obj.obj (op V),
      F.obj.map e.inv.op
        (((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j).app F).hom.app
          (op V) t) = s := by
  classical
  dsimp only
  let V := Scheme.Etale.mk (𝟙 Z)
  let W := Scheme.Etale.mk (𝟙 X)
  let e : j.Etale.obj V ≅ W :=
    ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Z).isTerminalObj
      j.Etale).uniqueUpToIso (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)
  have hj : SectionHasProperSupport Λ F W j s := by
    obtain ⟨T, hT, hp⟩ := (sectionHasProperSupport_iff Λ F W f s).1 hs
    apply (sectionHasProperSupport_iff Λ F W j s).2
    refine ⟨T, hT, ?_⟩
    have : IsProper
        (((IdealSheafData.vanishingIdeal T).subschemeι ≫ j) ≫ p) := by
      rw [Category.assoc, hf]
      exact hp
    exact IsProper.of_comp _ p
  have he : e.hom.left ≫ j = pullback.fst V.hom j := by
    have hw : e.hom.left = pullback.snd V.hom j := by
      have hw := e.hom.w
      change e.hom.left ≫ 𝟙 X = pullback.snd V.hom j ≫ 𝟙 X at hw
      exact (Category.comp_id e.hom.left).symm.trans
        (hw.trans (Category.comp_id (pullback.snd V.hom j)))
    rw [hw, ← pullback.condition]
    exact Category.comp_id _
  have hs' : SectionHasProperSupport Λ F (j.Etale.obj V)
      (pullback.fst V.hom j) (F.obj.map e.hom.op s) :=
    (section_support_iso_iff Λ F e (pullback.fst V.hom j) j he s).2 hj
  obtain ⟨t, ht⟩ := (openExtensionProperSupport_range Λ j F V).2 _ |>.2 hs'
  refine ⟨t, ?_⟩
  change F.obj.map e.inv.op _ = s
  rw [ht, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    e.inv_hom_id, op_id, F.obj.map_id]
  rfl

private theorem sheaf_sections_exact
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hS : S.ShortExact) (V : X.Etale) (s : S.X₂.obj.obj (op V))
    (hs : S.g.hom.app (op V) s = 0) :
    ∃ t, S.f.hom.app (op V) t = s := by
  let E := (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op V)
  have : PreservesFiniteLimits E := by
    change PreservesFiniteLimits
      (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        (CategoryTheory.evaluation _ _).obj (op V))
    infer_instance
  have : E.Additive := Functor.additive_of_preserves_binary_products E
  have hE := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono E).1
    inferInstance S hS
  exact (ShortComplex.moduleCat_exact_iff (S.map E)).1 hE.1 s hs

set_option backward.isDefEq.respectTransparency false in
private theorem open_counit_section_lift
    (Λ : Type (u + 1)) [CommRing Λ] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale)
    (s : F.obj.obj (op V))
    (hs : ∀ (K : Type u) [Field K] [IsSepClosed K] (k : Spec (.of K) ⟶ V.left),
      V.hom (k default) ∉ Set.range j →
        (pointSmallEtale (k ≫ V.hom)).toPresheafFiber V (Over.homMk k) F.obj s = 0) :
    ∃ t, ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app
      F).hom.app (op V) t = s := by
  classical
  let T : TopologicalSpace.Closeds X :=
    ⟨(Set.range j)ᶜ, (IsOpenImmersion.isOpen_range j).isClosed_compl⟩
  let d := (IdealSheafData.vanishingIdeal T).subschemeι
  have hd : Set.range d.base = (Set.range j.base)ᶜ := by simp [d, T]
  let S := openClosedShortComplex (ModuleCat.{u + 1} Λ) j d
    (disjoint_range_of_range_eq_compl j d hd) F
  have hS := shortExact_openClosedShortComplex (ModuleCat.{u + 1} Λ) j d F hd
  apply sheaf_sections_exact Λ S hS V s
  change ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) d).unit.app F).hom.app
    (op V) s = 0
  apply module_section_zero_of_germs Λ
    ((upperStar (ModuleCat.{u + 1} Λ) d).obj F) (d.Etale.obj V)
  intro K _ _ k
  have h := pullback_restrict_germ_zero Λ d F V (d.Etale.obj V) (𝟙 (d.Etale.obj V)) s k
  simp only [op_id, ((upperStar (ModuleCat.{u + 1} Λ) d).obj F).obj.map_id,
    ConcreteCategory.id_apply] at h
  apply h.2
  change (pointSmallEtale ((k ≫ pullback.fst V.hom d) ≫ V.hom)).toPresheafFiber
    V (Over.homMk (k ≫ pullback.fst V.hom d)) F.obj s = 0
  apply hs K (k ≫ pullback.fst V.hom d)
  change V.hom (pullback.fst V.hom d (k default)) ∉ Set.range j
  have he := congrArg (fun a ↦ a (k default))
    (pullback.condition (f := V.hom) (g := d))
  change V.hom (pullback.fst V.hom d (k default)) =
    d (pullback.snd V.hom d (k default)) at he
  have hm : d (pullback.snd V.hom d (k default)) ∈ Set.range d := ⟨_, rfl⟩
  have hm' : d (pullback.snd V.hom d (k default)) ∉ Set.range j := by
    rwa [hd] at hm
  exact he.symm ▸ hm'

private theorem compact_support_neighbourhood
    {X Y X' : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (b : X' ⟶ X) (q : X' ⟶ Spec (.of Ω)) [LocallyOfFiniteType q] (sq : CommSq b q f y)
    (T : TopologicalSpace.Closeds X')
    (hT : IsClosedSubsetProperOver q T) :
    ∃ (U : Y.Opens) (W : X.Opens), IsAffineOpen U ∧ IsCompact (W : Set X) ∧
      y default ∈ U ∧ W ≤ f ⁻¹ᵁ U ∧
      b '' (T : Set X') ⊆ (W : Set X) := by
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := y default) (U := ⊤) trivial
  let d := (IdealSheafData.vanishingIdeal T).subschemeι
  have : IsProper (d ≫ q) := hT
  have : CompactSpace (IdealSheafData.vanishingIdeal T).subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (d ≫ q)
  have hTc : IsCompact (T : Set X') := by
    have hd : Set.range d = (T : Set X') := by simp [d]
    rw [← hd]
    exact isCompact_range d.continuous
  have hc := hTc.image b.continuous
  have hsub : b '' (T : Set X') ⊆
      (f ⁻¹ᵁ U : Set X) := by
    rintro _ ⟨x, _, rfl⟩
    change f (b x) ∈ U
    have he := congrArg (fun a ↦ a x) sq.w
    change f (b x) = y (q x) at he
    rw [he, Subsingleton.elim (q x) default]
    exact hyU
  obtain ⟨W, hWc, hWo, hTW, hWU⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hc (f ⁻¹ᵁ U).isOpen hsub
  exact ⟨U, ⟨W, hWo⟩, hU, hWc, hyU, hWU, hTW⟩

set_option backward.isDefEq.respectTransparency false in
private noncomputable def compactSupportComparison
    (Λ : Type (u + 1)) [CommRing Λ] {X Z Y : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (lowerStar (ModuleCat.{u + 1} Λ) p).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj F) ⟶
      (lowerStar (ModuleCat.{u + 1} Λ) (j ≫ p)).obj F :=
  (lowerStar (ModuleCat.{u + 1} Λ) p).map
      ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j).app F) ≫
    (lowerStarComp (ModuleCat.{u + 1} Λ) j p).hom.app F

set_option backward.isDefEq.respectTransparency false in
private theorem compactSupportComparison_range
    (Λ : Type (u + 1)) [CommRing Λ] {X Z Y : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y.Etale)
    (s : F.obj.obj (op ((j ≫ p).Etale.obj V))) :
    (∃ t, (compactSupportComparison Λ j p F).hom.app (op V) t = s) ↔
      SectionHasProperSupport Λ F ((j ≫ p).Etale.obj V)
        (pullback.fst V.hom (j ≫ p)) s := by
  let W := p.Etale.obj V
  let B := j.Etale.obj W
  let C := (j ≫ p).Etale.obj V
  let e : C ≅ B := (MorphismProperty.Over.pullbackComp j p).app V
  let a := pullback.fst W.hom j
  let b := pullback.fst V.hom p
  let r := pullback.fst V.hom (j ≫ p)
  have he : e.hom.left ≫ (a ≫ b) = r :=
    MorphismProperty.Over.pullbackComp_left_fst_fst j p V
  have hc (t : F.obj.obj (op B)) := section_support_iso_iff Λ F e r (a ≫ b) he t
  have hab (t : F.obj.obj (op B)) :
      SectionHasProperSupport Λ F B a t ↔ SectionHasProperSupport Λ F B (a ≫ b) t := by
    constructor
    · rintro ⟨T, hT, hp⟩
      refine ⟨T, hT, ?_⟩
      have : IsProper ((IdealSheafData.vanishingIdeal T).subschemeι ≫ a) := hp
      change IsProper ((IdealSheafData.vanishingIdeal T).subschemeι ≫ a ≫ b)
      rw [← Category.assoc]
      infer_instance
    · rintro ⟨T, hT, hp⟩
      refine ⟨T, hT, ?_⟩
      have : IsProper (((IdealSheafData.vanishingIdeal T).subschemeι ≫ a) ≫ b) := by
        change IsProper ((IdealSheafData.vanishingIdeal T).subschemeι ≫ (a ≫ b)) at hp
        simpa only [Category.assoc] using hp
      exact IsProper.of_comp _ b
  have hmap (t : ((lowerStar (ModuleCat.{u + 1} Λ) p).obj
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj F)).obj.obj (op V)) :
      (compactSupportComparison Λ j p F).hom.app (op V) t =
        F.obj.map e.hom.op
          (((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j).app F).hom.app
            (op W) t) := by
    change ((lowerStarComp (ModuleCat.{u + 1} Λ) j p).hom.app F).hom.app (op V)
      (((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j).app F).hom.app
        (op W) t) = _
    rw [lowerStarComp_hom_app_hom_app]
    rfl
  constructor
  · rintro ⟨t, rfl⟩
    rw [hmap]
    apply (hc _).2
    apply (hab _).1
    exact (openExtensionProperSupport_range Λ j F W).2 _ |>.1 ⟨t, rfl⟩
  · intro hs
    let s₀ := F.obj.map e.inv.op s
    have hback : F.obj.map e.hom.op s₀ = s := by
      dsimp only [s₀]
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      simp
    have hs₀ : SectionHasProperSupport Λ F B a s₀ :=
      (hab _).2 ((hc _).1 (hback.symm ▸ hs))
    obtain ⟨t, ht⟩ := (openExtensionProperSupport_range Λ j F W).2 _ |>.2 hs₀
    exact ⟨t, (hmap t).trans (congrArg (F.obj.map e.hom.op) ht |>.trans hback)⟩

private theorem section_support_map
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}}
    {F H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (α : F ⟶ H)
    (V : X.Etale) (p : V.left ⟶ S) [LocallyOfFiniteType p]
    (s : F.obj.obj (op V)) (hs : SectionHasProperSupport Λ F V p s) :
    SectionHasProperSupport Λ H V p (α.hom.app (op V) s) := by
  classical
  obtain ⟨C, hC, hp⟩ := (sectionHasProperSupport_iff Λ F V p s).1 hs
  obtain ⟨D, hD, hDa⟩ := etaleModuleSection_closedSupport Λ H V (α.hom.app (op V) s)
  refine ⟨D, hDa, (closed_subset_proper_over_base_properties p C).2.2.1 D ?_ hp⟩
  intro x hx
  let K := AlgebraicClosure (V.left.residueField x)
  let k := V.left.algClosurePoint x
  have hk : k default = x := Scheme.algClosurePoint_base _ _ _
  have hn := (hD K k).1 (hk.symm ▸ hx)
  apply hk ▸ (hC K k).2
  intro hz
  have he := (pointSmallEtale (k ≫ V.hom)).toPresheafFiber_naturality_apply
    α.hom V (Over.homMk k) s
  rw [hz, map_zero] at he
  exact hn he.symm

set_option backward.isDefEq.respectTransparency false in
private theorem closed_support_open_restrict
    {X U S : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (p : X ⟶ S) [LocallyOfFiniteType p] [IsSeparated p]
    (C : TopologicalSpace.Closeds X) (hp : IsClosedSubsetProperOver p C)
    (hC : (C : Set X) ⊆ Set.range j) :
    IsClosedSubsetProperOver (j ≫ p) (C.preimage j.continuous) := by
  let d := (IdealSheafData.vanishingIdeal C).subschemeι
  have hd : Set.range d = (C : Set X) := by simp [d]
  let k := IsOpenImmersion.lift j d (hd.trans_subset hC)
  have hk : k ≫ j = d := IsOpenImmersion.lift_fac _ _ _
  have : IsClosedImmersion (k ≫ j) := by rw [hk]; infer_instance
  have sq : IsPullback (𝟙 _) k d j :=
    IsPullback.of_horiz_isIso_mono ⟨by simpa only [Category.id_comp] using hk.symm⟩
  have : IsClosedImmersion k := MorphismProperty.of_isPullback sq inferInstance
  have hr : Set.range k = (C.preimage j.continuous : Set U) := by
    ext x
    change (∃ z, k z = x) ↔ j x ∈ C
    constructor
    · rintro ⟨z, rfl⟩
      have hz : d z ∈ (C : Set X) := by rw [← hd]; exact Set.mem_range_self z
      exact (congrArg (fun a ↦ a z) hk).symm ▸ hz
    · intro hx
      have hx' : j x ∈ (C : Set X) := hx
      rw [← hd] at hx'
      obtain ⟨z, hz⟩ := hx'
      refine ⟨z, j.isOpenEmbedding.injective ?_⟩
      exact (congrArg (fun a ↦ a z) hk).trans hz
  apply (closed_subset_proper_over_base_properties (j ≫ p)
    (C.preimage j.continuous)).1.2
  refine ⟨_, k, inferInstance, hr, ?_⟩
  rw [← Category.assoc, hk]
  exact hp

set_option backward.isDefEq.respectTransparency false in
private noncomputable def openExtensionSupportComparison
    (Λ : Type (u + 1)) [CommRing Λ] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj F ⟶
      (properSupportLowerStar Λ j).obj F where
  hom :=
    { app := fun V ↦ ModuleCat.ofHom
        { toFun := fun s ↦
            ⟨((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j).app F).hom.app
              V s, (openExtensionProperSupport_range Λ j F V.unop).2 _ |>.1 ⟨s, rfl⟩⟩
          map_add' := fun s t ↦ Subtype.ext (map_add _ _ _)
          map_smul' := fun r s ↦ Subtype.ext (map_smul _ _ _) }
      naturality := by
        intro V W h
        apply ModuleCat.hom_ext
        ext s
        apply Subtype.ext
        exact ConcreteCategory.congr_hom
          (((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j).app F).hom.naturality
            h) s }

set_option backward.isDefEq.respectTransparency false in
private theorem openExtensionSupportComparison_isIso
    (Λ : Type (u + 1)) [CommRing Λ] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (openExtensionSupportComparison Λ j F) := by
  let q := openExtensionSupportComparison Λ j F
  have hq (V : X.Etaleᵒᵖ) : IsIso (q.hom.app V) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    constructor
    · intro s t h
      exact (openExtensionProperSupport_range Λ j F V.unop).1
        (congrArg Subtype.val h)
    · rintro ⟨s, hs⟩
      obtain ⟨t, ht⟩ := (openExtensionProperSupport_range Λ j F V.unop).2 s |>.2 hs
      exact ⟨t, Subtype.ext ht⟩
  have : IsIso ((sheafToPresheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).map q) := by
    change IsIso q.hom
    exact NatIso.isIso_of_isIso_app q.hom
  exact isIso_of_reflects_iso q (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def terminalPullbackIso {U X : Scheme.{u}} (j : U ⟶ X) :
    j.Etale.obj (Scheme.Etale.mk (𝟙 X)) ≅ Scheme.Etale.mk (𝟙 U) :=
  ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X).isTerminalObj
    j.Etale).uniqueUpToIso
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale U)

private noncomputable def topPushIso
    (Λ : Type (u + 1)) [CommRing Λ] {U X : Scheme.{u}} (j : U ⟶ X)
    (E : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((j)_*[ModuleCat.{u + 1} Λ].obj E).obj.obj (op (Scheme.Etale.mk (𝟙 X))) ≅
      E.obj.obj (op (Scheme.Etale.mk (𝟙 U))) :=
  E.obj.mapIso (terminalPullbackIso j).op.symm

private noncomputable def topPull
    (Λ : Type (u + 1)) [CommRing Λ] {U X : Scheme.{u}} (j : U ⟶ X)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    F.obj.obj (op (Scheme.Etale.mk (𝟙 X))) ⟶
      ((j)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (Scheme.Etale.mk (𝟙 U))) :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app F).hom.app
    (op (Scheme.Etale.mk (𝟙 X))) ≫
      (topPushIso Λ j ((j)^*[ModuleCat.{u + 1} Λ].obj F)).hom

set_option backward.isDefEq.respectTransparency false in
private theorem topPull_open_properSupport
    (Λ : Type (u + 1)) [CommRing Λ] {U X S : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (p : X ⟶ S)
    [IsSeparated p] [LocallyOfFiniteType p]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (s : F.obj.obj (op (Scheme.Etale.mk (𝟙 X))))
    (hs : SectionHasProperSupport Λ F (Scheme.Etale.mk (𝟙 X)) p s)
    (hzero : ∀ (K : Type u) [Field K] [IsSepClosed K] (k : Spec (.of K) ⟶ X),
      k default ∉ Set.range j →
        (pointSmallEtale k).toPresheafFiber (Scheme.Etale.mk (𝟙 X))
          (Over.homMk k (Category.comp_id k)) F.obj s = 0) :
    SectionHasProperSupport Λ ((j)^*[ModuleCat.{u + 1} Λ].obj F)
      (Scheme.Etale.mk (𝟙 U)) (j ≫ p) (topPull Λ j F s) := by
  classical
  obtain ⟨T, hT, hp⟩ := (sectionHasProperSupport_iff Λ F _ p s).1 hs
  change TopologicalSpace.Closeds X at T
  have hTr : (T : Set X) ⊆ Set.range j := by
    intro x hx
    by_contra hn
    let K := AlgebraicClosure (X.residueField x)
    let k := X.algClosurePoint x
    have hk : k default = x := Scheme.algClosurePoint_base _ _ _
    have hz := hzero K k (hk.symm ▸ hn)
    have htk := hT K k
    have hpt : k ≫ (Scheme.Etale.mk (𝟙 X)).hom = k := Category.comp_id k
    have hz' := (germ_zero_change_point Λ F _ s (k ≫ 𝟙 X) k hpt k rfl hpt).2 hz
    exact (htk.1 (hk.symm ▸ hx)) hz'
  let V := Scheme.Etale.mk (𝟙 X)
  let W := Scheme.Etale.mk (𝟙 U)
  let h := (terminalPullbackIso j).inv
  let a := h.left ≫ pullback.fst V.hom j
  have ha : a = j := by
    have he : h.left ≫ pullback.snd (𝟙 X) j = 𝟙 U := h.w
    dsimp only [a, V]
    have hh := congrArg (fun z : U ⟶ U ↦ z ≫ j) he
    erw [Category.assoc, ← pullback.condition, Category.comp_id] at hh
    exact hh
  apply (sectionHasProperSupport_iff Λ _ W (j ≫ p) _).2
  refine ⟨T.preimage a.continuous, ?_, ?_⟩
  · intro K _ _ k
    have ht := hT K ((k ≫ h.left) ≫ pullback.fst V.hom j)
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at ht
    exact ht.trans (not_congr (pullback_restrict_germ_zero Λ j F V W h s k)).symm
  · rw [ha]
    exact closed_support_open_restrict j p T hp hTr

set_option backward.isDefEq.respectTransparency false in
private theorem openCounit_comp_unit
    (Λ : Type (u + 1)) [CommRing Λ] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app F ≫
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j).app
        ((j)^*[ModuleCat.{u + 1} Λ].obj F) := by
  let A := ModuleCat.{u + 1} Λ
  apply openImmersionLowerShriek_lowerStar_hom_ext A j
  rw [Functor.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% (openImmersionLowerShriekUpperStarAdjunction A j).right_triangle_components F]
  erw [(upperStarLowerStarAdjunction A j).left_triangle_components F]
  symm
  exact unit_map_openImmersionLowerShriekToLowerStar_app_counit A j _

set_option backward.isDefEq.respectTransparency false in
private theorem openCounit_topPull_injective
    (Λ : Type (u + 1)) [CommRing Λ] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Injective
      (((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app
        F).hom.app (op (Scheme.Etale.mk (𝟙 X))) ≫ topPull Λ j F) := by
  let A := ModuleCat.{u + 1} Λ
  have h := NatTrans.congr_app (Sheaf.hom_ext_iff.1 (openCounit_comp_unit Λ j F))
    (op (Scheme.Etale.mk (𝟙 X)))
  change _ ≫ _ = _ at h
  unfold topPull
  rw [← Category.assoc, h]
  exact ((ConcreteCategory.isIso_iff_bijective
    (topPushIso Λ j ((j)^*[A].obj F)).hom).1 inferInstance).1.comp
      (openExtensionProperSupport_range Λ j ((j)^*[A].obj F) _).1

set_option backward.isDefEq.respectTransparency false in
private theorem openBaseChange_counit
    (Λ : Type (u + 1)) [CommRing Λ] {U X U' X' : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (j' : U' ⟶ X') [IsOpenImmersion j']
    (a : U' ⟶ U) (b : X' ⟶ X) (sq : CommSq a j' j b)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app
        ((j)^*[ModuleCat.{u + 1} Λ].obj F) ≫
      ((b)^*[ModuleCat.{u + 1} Λ]).map
        ((openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} Λ) j).counit.app F) =
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j').map
        ((squareUpperStarIso (ModuleCat.{u + 1} Λ) sq).inv.app F) ≫
      (openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} Λ) j').counit.app ((b)^*[ModuleCat.{u + 1} Λ].obj F) := by
  let A := ModuleCat.{u + 1} Λ
  apply ((openImmersionLowerShriekUpperStarAdjunction A j').homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp]
  erw [reassoc_of% unit_map_openImmersionLowerShriekBaseChangeMap_app A sq]
  erw [← (squareUpperStarIso A sq.flip).hom.naturality
    ((openImmersionLowerShriekUpperStarAdjunction A j).counit.app F)]
  change _ ≫ (a)^*[A].map ((j)^*[A].map _) ≫ _ = _
  rw [← Functor.map_comp_assoc]
  erw [(openImmersionLowerShriekUpperStarAdjunction A j).right_triangle_components F]
  erw [← reassoc_of% (openImmersionLowerShriekUpperStarAdjunction A j').unit.naturality
    ((squareUpperStarIso A sq).inv.app F)]
  erw [(openImmersionLowerShriekUpperStarAdjunction A j').right_triangle_components
    ((b)^*[A].obj F)]
  simp only [Category.comp_id]
  erw [((a)^*[A]).map_id, Category.id_comp]
  exact congrArg (fun e ↦ e.hom.app F) (squareUpperStarIso_flip A sq)

set_option backward.isDefEq.respectTransparency false in
private theorem openSource_support_lift
    (Λ : Type (u + 1)) [CommRing Λ] {U X Y : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y.Etale)
    (t : ((j)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj
      (op ((j ≫ f).Etale.obj V)))
    (ht : SectionHasProperSupport Λ ((j)^*[ModuleCat.{u + 1} Λ].obj F)
      ((j ≫ f).Etale.obj V) (pullback.fst V.hom (j ≫ f)) t) :
    let E := (j)^*[ModuleCat.{u + 1} Λ].obj F
    let e := (MorphismProperty.Over.pullbackComp
      (P := @AlgebraicGeometry.Etale) (Q := ⊤) j f).app V
    ∃ (r : ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj E).obj.obj
        (op (f.Etale.obj V))),
      SectionHasProperSupport Λ ((openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) j).obj E) (f.Etale.obj V) (pullback.fst V.hom f) r ∧
      ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j).app E).hom.app
          (op (f.Etale.obj V)) r = E.obj.map e.inv.op t := by
  dsimp only
  let A := ModuleCat.{u + 1} Λ
  let E := (j)^*[A].obj F
  let e := (MorphismProperty.Over.pullbackComp
    (P := @AlgebraicGeometry.Etale) (Q := ⊤) j f).app V
  let q := openExtensionSupportComparison Λ j E
  have : IsIso q := openExtensionSupportComparison_isIso Λ j E
  obtain ⟨σ, hσ⟩ := (properSupportComposite_range Λ j f E V t).2 ht
  let r := (inv q).hom.app (op (f.Etale.obj V)) σ.val
  refine ⟨r, section_support_map Λ (inv q) _ _ σ.val σ.property, ?_⟩
  have hq : q.hom.app (op (f.Etale.obj V)) r = σ.val := by
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (Sheaf.hom_ext_iff.1 (IsIso.inv_hom_id q))
        (op (f.Etale.obj V))) σ.val
  have hv := congrArg Subtype.val hq
  change ((openImmersionLowerShriekToLowerStar A j).app E).hom.app
      (op (f.Etale.obj V)) r = σ.val.val at hv
  rw [hv]
  have hσ' : E.obj.map e.hom.op σ.val.val = t := by
    change ((lowerStarComp A j f).hom.app E).hom.app (op V) σ.val.val = t at hσ
    rw [lowerStarComp_hom_app_hom_app] at hσ
    exact hσ
  rw [← hσ', ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    e.inv_hom_id, op_id, E.obj.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem fibre_restriction_sheaf_naturality
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {a : X' ⟶ X} {q : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {y : Spec (.of Ω) ⟶ Y} (sq : CommSq a q f y)
    {E F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (α : E ⟶ F)
    (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V) :
    α.hom.app (op (f.Etale.obj V)) ≫ geometricFibreSectionRestriction Λ sq F V v =
      geometricFibreSectionRestriction Λ sq E V v ≫
        (((a)^*[ModuleCat.{u + 1} Λ]).map α).hom.app
          (op (Scheme.Etale.mk (𝟙 X'))) := by
  unfold geometricFibreSectionRestriction
  have hu := NatTrans.congr_app (Sheaf.hom_ext_iff.1
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).unit.naturality α))
      (op (f.Etale.obj V))
  change _ ≫ _ = _ ≫ _ at hu
  rw [← Category.assoc]
  erw [hu]
  simp only [Category.assoc]
  congr 1
  exact ((((a)^*[ModuleCat.{u + 1} Λ]).map α).hom.naturality
    (geometricFibreSectionLift sq V v).op).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem fibre_restriction_composition
    (Λ : Type (u + 1)) [CommRing Λ]
    {X Z Y X' Z' : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (j : X ⟶ Z) (p : Z ⟶ Y) (a : X' ⟶ X) (b : Z' ⟶ Z)
    (j' : X' ⟶ Z') (q : Z' ⟶ Spec (.of Ω)) (y : Spec (.of Ω) ⟶ Y)
    (sqj : CommSq a j' j b) (sqp : CommSq b q p y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V) :
    let sqf : CommSq a (j' ≫ q) (j ≫ p) y :=
      ⟨by rw [← Category.assoc, sqj.w, Category.assoc, sqp.w, Category.assoc]⟩
    let e : j'.Etale.obj (Scheme.Etale.mk (𝟙 Z')) ≅ Scheme.Etale.mk (𝟙 X') :=
      ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Z').isTerminalObj
        j'.Etale).uniqueUpToIso
          (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X')
    ((lowerStarComp (ModuleCat.{u + 1} Λ) j p).hom.app F).hom.app (op V) ≫
        geometricFibreSectionRestriction Λ sqf F V v =
      geometricFibreSectionRestriction Λ sqp ((j)_*[ModuleCat.{u + 1} Λ].obj F) V v ≫
        ((baseChangeMap (ModuleCat.{u + 1} Λ) sqj).app F).hom.app
          (op (Scheme.Etale.mk (𝟙 Z'))) ≫
        (((a)^*[ModuleCat.{u + 1} Λ].obj F).obj.map e.inv.op) := by
  dsimp only
  let A := ModuleCat.{u + 1} Λ
  let H := (a)^*[A].obj F
  let e : j'.Etale.obj (Scheme.Etale.mk (𝟙 Z')) ≅ Scheme.Etale.mk (𝟙 X') :=
    ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Z').isTerminalObj
      j'.Etale).uniqueUpToIso
        (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X')
  let sqf : CommSq a (j' ≫ q) (j ≫ p) y :=
    ⟨by rw [← Category.assoc, sqj.w, Category.assoc, sqp.w, Category.assoc]⟩
  let l := geometricFibreSectionLift sqp V v
  let c := (MorphismProperty.Over.pullbackComp
    (P := @AlgebraicGeometry.Etale) (Q := ⊤) j p).app V
  let c₁ := MorphismProperty.Over.pullbackComp
    (P := @AlgebraicGeometry.Etale) (Q := ⊤) a j
  let c₂ := MorphismProperty.Over.pullbackComp
    (P := @AlgebraicGeometry.Etale) (Q := ⊤) j' b (a ≫ j) sqj.w
  rw [lowerStarComp_hom_app_hom_app]
  unfold geometricFibreSectionRestriction
  rw [← Category.assoc]
  erw [((upperStarLowerStarAdjunction A a).unit.app F).hom.naturality c.hom.op]
  simp only [Category.assoc]
  have hn := ((baseChangeMap A sqj).app F).hom.naturality l.op
  change _ ≫ _ = _ ≫ _ at hn
  erw [reassoc_of% hn]
  have hu := unit_map_baseChangeMap_app A sqj F
  have huV := NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (op (p.Etale.obj V))
  change _ ≫ _ = _ ≫ _ at huV
  erw [reassoc_of% huV]
  change _ ≫ (H.obj.map (a.Etale.map c.hom).op ≫
      H.obj.map (geometricFibreSectionLift sqf V v).op) =
    _ ≫ (H.obj.map (c₁.hom.app (p.Etale.obj V)).op ≫
      H.obj.map (c₂.inv.app (p.Etale.obj V)).op ≫
      H.obj.map (j'.Etale.map l).op ≫ H.obj.map e.inv.op)
  congr 1
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  apply MorphismProperty.Over.Hom.ext
  have he : e.inv.left ≫ pullback.snd (𝟙 Z') j' = 𝟙 X' := e.inv.w
  have hefst : e.inv.left ≫ pullback.fst (𝟙 Z') j' = j' := by
    have h := congrArg (fun z : X' ⟶ X' ↦ z ≫ j') he
    erw [Category.assoc, ← pullback.condition, Category.comp_id] at h
    exact h
  change (geometricFibreSectionLift sqf V v).left ≫ (a.Etale.map c.hom).left =
    e.inv.left ≫ (j'.Etale.map l).left ≫ (c₂.inv.app (p.Etale.obj V)).left ≫
      (c₁.hom.app (p.Etale.obj V)).left
  dsimp only [Hom.Etale, MorphismProperty.Over.pullback_obj_left,
    MorphismProperty.Over.pullback_obj_hom, MorphismProperty.Over.pullback_map_left,
    MorphismProperty.Over.pullbackComp_inv_app_left,
    MorphismProperty.Over.pullbackComp_hom_app_left, c, c₁, c₂, l]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [geometricFibreSectionLift, Hom.Etale, Category.assoc, reassoc_of% hefst]
      · simp [geometricFibreSectionLift, Hom.Etale, Category.assoc,
          reassoc_of% hefst, sqj.w]
    · simp [geometricFibreSectionLift, Hom.Etale, Category.assoc, reassoc_of% he]
  · simpa [geometricFibreSectionLift, Hom.Etale, Category.assoc] using he.symm

set_option backward.isDefEq.respectTransparency false in
private theorem fibre_restriction_open_unit
    (Λ : Type (u + 1)) [CommRing Λ]
    {U X Y U' X' : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (j : U ⟶ X) (f : X ⟶ Y) (a : U' ⟶ U) (b : X' ⟶ X)
    (j' : U' ⟶ X') (q : X' ⟶ Spec (.of Ω)) (y : Spec (.of Ω) ⟶ Y)
    (sqj : CommSq a j' j b) (sqf : CommSq b q f y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V) :
    let A := ModuleCat.{u + 1} Λ
    let sqU : CommSq a (j' ≫ q) (j ≫ f) y :=
      ⟨by rw [← Category.assoc, sqj.w, Category.assoc, sqf.w, Category.assoc]⟩
    ((upperStarLowerStarAdjunction A j).unit.app F).hom.app (op (f.Etale.obj V)) ≫
        ((lowerStarComp A j f).hom.app ((j)^*[A].obj F)).hom.app (op V) ≫
          geometricFibreSectionRestriction Λ sqU ((j)^*[A].obj F) V v =
      geometricFibreSectionRestriction Λ sqf F V v ≫
        topPull Λ j' ((b)^*[A].obj F) ≫
          ((squareUpperStarIso A sqj).hom.app F).hom.app
            (op (Scheme.Etale.mk (𝟙 U'))) := by
  dsimp only
  let A := ModuleCat.{u + 1} Λ
  let E := (j)^*[A].obj F
  let H := (b)^*[A].obj F
  let S := (squareUpperStarIso A sqj).hom.app F
  rw [fibre_restriction_composition Λ j f a b j' q y sqj sqf E V v]
  rw [← Category.assoc]
  erw [fibre_restriction_sheaf_naturality Λ sqf
    ((upperStarLowerStarAdjunction A j).unit.app F) V v]
  simp only [Category.assoc]
  have h := NatTrans.congr_app (Sheaf.hom_ext_iff.1
    (map_unit_baseChangeMap_app A sqj F)) (op (Scheme.Etale.mk (𝟙 X')))
  change _ ≫ _ = _ ≫ _ at h
  erw [reassoc_of% h]
  unfold topPull
  simp only [Category.assoc]
  congr 1
  congr 1
  exact (S.hom.naturality (terminalPullbackIso j').inv.op).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem open_source_fibre_section_lift
    (Λ : Type (u + 1)) [CommRing Λ]
    {U X Y U' X' : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (j : U ⟶ X) [IsOpenImmersion j] (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f]
    (a : U' ⟶ U) (b : X' ⟶ X) (j' : U' ⟶ X') [IsOpenImmersion j']
    (q : X' ⟶ Spec (.of Ω)) [IsSeparated q] [LocallyOfFiniteType q]
    (y : Spec (.of Ω) ⟶ Y)
    (sqj : IsPullback a j' j b) (sqf : IsPullback b q f y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (s : ((b)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 X'))))
    (hs : SectionHasProperSupport Λ ((b)^*[ModuleCat.{u + 1} Λ].obj F)
      (Scheme.Etale.mk (𝟙 X')) q s)
    (hzero : ∀ (K : Type u) [Field K] [IsSepClosed K] (k : Spec (.of K) ⟶ X'),
      k default ∉ Set.range j' →
        (pointSmallEtale k).toPresheafFiber (Scheme.Etale.mk (𝟙 X'))
          (Over.homMk k) ((b)^*[ModuleCat.{u + 1} Λ].obj F).obj s = 0)
    (hLift : ∀ (s₀ : ((a)^*[ModuleCat.{u + 1} Λ].obj
        ((j)^*[ModuleCat.{u + 1} Λ].obj F)).obj.obj
          (op (Scheme.Etale.mk (𝟙 U')))),
      SectionHasProperSupport Λ ((a)^*[ModuleCat.{u + 1} Λ].obj
        ((j)^*[ModuleCat.{u + 1} Λ].obj F)) (Scheme.Etale.mk (𝟙 U')) (j' ≫ q) s₀ →
      ∃ (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V)
        (t : ((j)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op ((j ≫ f).Etale.obj V))),
        SectionHasProperSupport Λ ((j)^*[ModuleCat.{u + 1} Λ].obj F)
          ((j ≫ f).Etale.obj V) (pullback.fst V.hom (j ≫ f)) t ∧
        geometricFibreSectionRestriction Λ (sqj.paste_vert sqf).toCommSq
          ((j)^*[ModuleCat.{u + 1} Λ].obj F) V v t = s₀) :
    ∃ (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V)
      (t : F.obj.obj (op (f.Etale.obj V))),
      SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) t ∧
      geometricFibreSectionRestriction Λ sqf.toCommSq F V v t = s := by
  let A := ModuleCat.{u + 1} Λ
  let E := (j)^*[A].obj F
  let H := (b)^*[A].obj F
  let S := (squareUpperStarIso A sqj.toCommSq).app F
  let α := (openImmersionLowerShriekUpperStarAdjunction A j).counit.app F
  let α' := (openImmersionLowerShriekUpperStarAdjunction A j').counit.app H
  let β := (openImmersionLowerShriekBaseChangeMap A sqj.toCommSq).app E
  have : IsIso (openImmersionLowerShriekBaseChangeMap A sqj.toCommSq) :=
    isIso_openImmersionLowerShriekBaseChangeMap A sqj
  have : IsIso β := inferInstance
  let s₀ := S.hom.hom.app (op (Scheme.Etale.mk (𝟙 U'))) (topPull Λ j' H s)
  have hs₀ : SectionHasProperSupport Λ ((a)^*[A].obj E)
      (Scheme.Etale.mk (𝟙 U')) (j' ≫ q) s₀ :=
    section_support_map Λ S.hom _ _ _ (topPull_open_properSupport Λ j' q H s hs hzero)
  obtain ⟨V, v, t, ht, hts⟩ := hLift s₀ hs₀
  obtain ⟨r, hr, hrt⟩ := openSource_support_lift Λ j f F V t ht
  let u := α.hom.app (op (f.Etale.obj V)) r
  refine ⟨V, v, u, section_support_map Λ α _ _ r hr, ?_⟩
  let η := (upperStarLowerStarAdjunction A j).unit.app F
  let C := ((lowerStarComp A j f).hom.app E).hom.app (op V)
  have hu : C (η.hom.app (op (f.Etale.obj V)) u) = t := by
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (Sheaf.hom_ext_iff.1 (openCounit_comp_unit Λ j F))
        (op (f.Etale.obj V))) r
    change η.hom.app _ u = _ at h
    erw [h, hrt]
    dsimp only [C]
    erw [lowerStarComp_hom_app_hom_app, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp, Iso.hom_inv_id, op_id, E.obj.map_id]
    rfl
  have hpull : topPull Λ j' H (geometricFibreSectionRestriction Λ sqf.toCommSq F V v u) =
      topPull Λ j' H s := by
    apply ((ConcreteCategory.isIso_iff_bijective (S.hom.hom.app
      (op (Scheme.Etale.mk (𝟙 U'))))).1 inferInstance).1
    have h := ConcreteCategory.congr_hom
      (fibre_restriction_open_unit Λ j f a b j' q y sqj.toCommSq sqf.toCommSq F V v) u
    simp only [ConcreteCategory.comp_apply] at h
    change geometricFibreSectionRestriction Λ (sqj.paste_vert sqf).toCommSq E V v
      (C (η.hom.app (op (f.Etale.obj V)) u)) =
        S.hom.hom.app (op (Scheme.Etale.mk (𝟙 U')))
          (topPull Λ j' H (geometricFibreSectionRestriction Λ sqf.toCommSq F V v u)) at h
    have hts' : geometricFibreSectionRestriction Λ
        (sqj.paste_vert sqf).toCommSq E V v t = s₀ := hts
    change geometricFibreSectionRestriction Λ (sqj.paste_vert sqf).toCommSq
      E V v (C (η.hom.app _ u)) = _ at h
    exact h.symm.trans ((congrArg
      (geometricFibreSectionRestriction Λ (sqj.paste_vert sqf).toCommSq E V v) hu).trans hts')
  obtain ⟨z, hz⟩ := open_counit_section_lift Λ j' H (Scheme.Etale.mk (𝟙 X')) s (by
    intro K _ _ k hk
    simpa using (germ_zero_change_point Λ H _ s (k ≫ 𝟙 X') k
      (Category.comp_id k) k rfl (Category.comp_id k)).2 (hzero K k hk))
  let w := (inv β).hom.app (op (Scheme.Etale.mk (𝟙 X')))
    (geometricFibreSectionRestriction Λ sqf.toCommSq
      ((openImmersionLowerShriek A j).obj E) V v r)
  let z' := ((openImmersionLowerShriek A j').map S.inv).hom.app
    (op (Scheme.Etale.mk (𝟙 X'))) w
  have hz' : α'.hom.app (op (Scheme.Etale.mk (𝟙 X'))) z' =
      geometricFibreSectionRestriction Λ sqf.toCommSq F V v u := by
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (Sheaf.hom_ext_iff.1
        (openBaseChange_counit Λ j j' a b sqj.toCommSq F))
          (op (Scheme.Etale.mk (𝟙 X')))) w
    have hβ : β.hom.app (op (Scheme.Etale.mk (𝟙 X'))) w =
        geometricFibreSectionRestriction Λ sqf.toCommSq
          ((openImmersionLowerShriek A j).obj E) V v r := by
      exact ConcreteCategory.congr_hom
        (NatTrans.congr_app (Sheaf.hom_ext_iff.1 (IsIso.inv_hom_id β)) _) _
    have hn := ConcreteCategory.congr_hom
      (fibre_restriction_sheaf_naturality Λ sqf.toCommSq α V v) r
    change (((b)^*[A]).map α).hom.app _ (β.hom.app _ w) =
      α'.hom.app _ z' at h
    erw [hβ] at h
    exact h.symm.trans hn.symm
  have hzz : z' = z := (openCounit_topPull_injective Λ j' H) (by
    change topPull Λ j' H (α'.hom.app _ z') = topPull Λ j' H (α'.hom.app _ z)
    rw [hz', hz]
    exact hpull)
  rw [← hz', hzz, hz]

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2000 in
private theorem compactifiable_fibre_section_lift
    (Λ : Type (u + 1)) [CommRing Λ] {X Z Y : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    {X' Z' : Scheme.{u}} (a : X' ⟶ X) (b : Z' ⟶ Z)
    (j' : X' ⟶ Z') [IsOpenImmersion j'] (q : Z' ⟶ Spec (.of Ω))
    [LocallyOfFiniteType q]
    (sqj : IsPullback a j' j b) (sqp : IsPullback b q p y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (s : ((a)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 X'))))
    (hs : SectionHasProperSupport Λ ((a)^*[ModuleCat.{u + 1} Λ].obj F)
      (Scheme.Etale.mk (𝟙 X')) (j' ≫ q) s) :
    let sqf : CommSq a (j' ≫ q) (j ≫ p) y :=
      ⟨by rw [← Category.assoc, sqj.w, Category.assoc, sqp.w, Category.assoc]⟩
    ∃ (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V)
      (t : F.obj.obj (op ((j ≫ p).Etale.obj V))),
      SectionHasProperSupport Λ F ((j ≫ p).Etale.obj V)
        (pullback.fst V.hom (j ≫ p)) t ∧
      geometricFibreSectionRestriction Λ sqf F V v t = s := by
  dsimp only
  let A := ModuleCat.{u + 1} Λ
  have : IsProper q := MorphismProperty.of_isPullback sqp inferInstance
  let E := (openImmersionLowerShriek A j).obj F
  let H := (a)^*[A].obj F
  let α := (openImmersionLowerShriekToLowerStar A j).app F
  let β := (openImmersionLowerShriekBaseChangeMap A sqj.toCommSq).app F
  let e : j'.Etale.obj (Scheme.Etale.mk (𝟙 Z')) ≅ Scheme.Etale.mk (𝟙 X') :=
    ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Z').isTerminalObj
      j'.Etale).uniqueUpToIso
        (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X')
  obtain ⟨z, hz⟩ := open_extension_section_lift Λ j' q (j' ≫ q) rfl H s hs
  let z' := β.hom.app (op (Scheme.Etale.mk (𝟙 Z'))) z
  obtain ⟨V, v, t, ht⟩ := proper_fibre_section_lift Λ p y sqp E z'
  let t' := (compactSupportComparison Λ j p F).hom.app (op V) t
  refine ⟨V, v, t', (compactSupportComparison_range Λ j p F V t').1 ⟨t, rfl⟩, ?_⟩
  have hcomp := ConcreteCategory.congr_hom
    (fibre_restriction_composition Λ j p a b j' q y sqj.toCommSq sqp.toCommSq F V v)
      (α.hom.app (op (p.Etale.obj V)) t)
  change geometricFibreSectionRestriction Λ _ F V v t' = _ at hcomp
  rw [hcomp]
  simp only [ConcreteCategory.comp_apply]
  have hnat := ConcreteCategory.congr_hom
    (fibre_restriction_sheaf_naturality Λ sqp.toCommSq α V v) t
  change geometricFibreSectionRestriction Λ sqp.toCommSq
      ((j)_*[A].obj F) V v (α.hom.app _ t) =
    (((b)^*[A]).map α).hom.app _
      (geometricFibreSectionRestriction Λ sqp.toCommSq E V v t) at hnat
  erw [hnat, ht]
  have hβ := openImmersionLowerShriekBaseChangeMap_comp_baseChangeMap_app A sqj.toCommSq F
  have hzβ := ConcreteCategory.congr_hom
    (NatTrans.congr_app (Sheaf.hom_ext_iff.1 hβ) (op (Scheme.Etale.mk (𝟙 Z')))) z
  change ((baseChangeMap A sqj.toCommSq).app F).hom.app _
      ((((b)^*[A]).map α).hom.app _ z') =
    ((openImmersionLowerShriekToLowerStar A j').app H).hom.app _ z at hzβ
  erw [hzβ]
  exact hz

set_option backward.isDefEq.respectTransparency false in
private theorem nagata_fibre_section_lift
    (Λ : Type (u + 1)) [CommRing Λ] {X Y X' : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [HasCompactification f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (a : X' ⟶ X) (q : X' ⟶ Spec (.of Ω)) [LocallyOfFiniteType q]
    (sq : IsPullback a q f y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (s : ((a)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 X'))))
    (hs : SectionHasProperSupport Λ ((a)^*[ModuleCat.{u + 1} Λ].obj F)
      (Scheme.Etale.mk (𝟙 X')) q s) :
    ∃ (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V)
      (t : F.obj.obj (op (f.Etale.obj V))),
      SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) t ∧
      geometricFibreSectionRestriction Λ sq.toCommSq F V v t = s := by
  rcases HasCompactification.compactification f with ⟨Z, p, j, hf, hp, hj⟩
  subst f
  let C : Compactification (j ≫ p) := ⟨Z, p, j, rfl, hp, hj⟩
  let D := C.ofIsPullback sq
  have hs' : SectionHasProperSupport Λ ((a)^*[ModuleCat.{u + 1} Λ].obj F)
      (Scheme.Etale.mk (𝟙 X')) (D.i ≫ D.g) s := by
    simpa only [← D.comm] using hs
  have h := compactifiable_fibre_section_lift Λ j p y a (pullback.fst p y)
    D.i D.g (C.isPullback_i_ofIsPullback sq)
      (C.isPullback_g_ofIsPullback sq).flip F s hs'
  simpa only [← D.comm] using h

set_option backward.isDefEq.respectTransparency false in
private theorem qcqs_fibre_section_lift
    (Λ : Type (u + 1)) [CommRing Λ] {X Y X' : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (b : X' ⟶ X) (q : X' ⟶ Spec (.of Ω)) [LocallyOfFiniteType q]
    (sq : IsPullback b q f y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (s : ((b)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 X'))))
    (hs : SectionHasProperSupport Λ ((b)^*[ModuleCat.{u + 1} Λ].obj F)
      (Scheme.Etale.mk (𝟙 X')) q s) :
    ∃ (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V)
      (t : F.obj.obj (op (f.Etale.obj V))),
      SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) t ∧
      geometricFibreSectionRestriction Λ sq.toCommSq F V v t = s := by
  classical
  let A := ModuleCat.{u + 1} Λ
  let H := (b)^*[A].obj F
  have : IsSeparated q := MorphismProperty.of_isPullback sq inferInstance
  obtain ⟨T, hT, hp⟩ := (sectionHasProperSupport_iff Λ H _ q s).1 hs
  change TopologicalSpace.Closeds X' at T
  obtain ⟨B, W, _, hW, _, _, hTW⟩ :=
    compact_support_neighbourhood f y b q sq.toCommSq T hp
  have : CompactSpace W := isCompact_iff_compactSpace.1 hW
  let j := W.ι
  let a := b ∣_ W
  let j' := (b ⁻¹ᵁ W).ι
  have sqj : IsPullback a j' j b := isPullback_morphismRestrict b W
  apply open_source_fibre_section_lift Λ j f a b j' q y sqj sq F s hs
  · intro K _ _ k hk
    by_contra hn
    have hkT : k default ∈ (T : Set X') := by
      have ht := hT K k
      exact ht.2 ((germ_zero_change_point Λ H _ s (k ≫ 𝟙 X') k
        (Category.comp_id k) k rfl (Category.comp_id k)).not.2 hn)
    have hw := hTW ⟨k default, hkT, rfl⟩
    apply hk
    change k default ∈ Set.range (b ⁻¹ᵁ W).ι
    rw [Scheme.Opens.range_ι]
    exact hw
  · intro s₀ hs₀
    exact nagata_fibre_section_lift Λ (j ≫ f) y a (j' ≫ q)
      (sqj.paste_vert sq) ((j)^*[A].obj F) s₀ hs₀

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem localized_unit_restriction
    (Λ : Type (u + 1)) [CommRing Λ] {T X : Scheme.{u}}
    (a : T ⟶ X) [Etale a]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : X.Etale) (W : T.Etale) (h : W ⟶ a.Etale.obj V) :
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).unit.app F).hom.app (op V) ≫
        ((a)^*[ModuleCat.{u + 1} Λ].obj F).obj.map h.op ≫
        ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) a inferInstance).hom.app
          F).hom.app (op W) =
      F.obj.map (((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ a inferInstance
        _root_.trivial).homEquiv W V).symm h).op := by
  let A := ModuleCat.{u + 1} Λ
  let ρ := (upperStarIsoLocalizationRestriction A a inferInstance).hom.app F
  have hu := congrArg (fun α ↦ α.hom.app (op V))
    (Adjunction.unit_leftAdjointUniq_hom_app (upperStarLowerStarAdjunction A a)
      (localizationRestrictionLowerStarAdjunction A a inferInstance) F)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hu
  rw [ρ.hom.naturality, ← Category.assoc]
  erw [show ((upperStarLowerStarAdjunction A a).unit.app F).hom.app (op V) ≫
    ρ.hom.app (op (a.Etale.obj V)) =
    ((localizationRestrictionLowerStarAdjunction A a inferInstance).unit.app F).hom.app
      (op V) from hu]
  change (𝟙 _ ≫ F.obj.map _ ≫ 𝟙 _) ≫ F.obj.map _ = _
  simp only [Category.id_comp, Category.comp_id, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem section_composition_unit
    (Λ : Type (u + 1)) [CommRing Λ] {T Z X : Scheme.{u}}
    (a : T ⟶ Z) (b : Z ⟶ X) (c : T ⟶ X) (hc : c = a ≫ b)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : X.Etale) (W : T.Etale) (h : W ⟶ c.Etale.obj V) :
    let A := ModuleCat.{u + 1} Λ
    ((upperStarLowerStarAdjunction A c).unit.app F).hom.app (op V) ≫
        ((c)^*[A].obj F).obj.map h.op ≫
        ((upperStarComp A a b c hc).hom.app F).hom.app (op W) =
      ((upperStarLowerStarAdjunction A b).unit.app F).hom.app (op V) ≫
        ((upperStarLowerStarAdjunction A a).unit.app ((b)^*[A].obj F)).hom.app
          (op (b.Etale.obj V)) ≫
        ((a)^*[A].obj ((b)^*[A].obj F)).obj.map
          (h ≫ (MorphismProperty.Over.pullbackComp
            (P := @Etale) (Q := ⊤) a b c hc).hom.app V).op := by
  dsimp only
  let A := ModuleCat.{u + 1} Λ
  have hh := congrArg (fun α ↦ α.hom.app (op V))
    (upperStarComp_hom_app_unit_app A a b F c hc)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Adjunction.comp_unit_app, lowerStarComp,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app] at hh
  rw [((upperStarComp A a b c hc).hom.app F).hom.naturality, ← Category.assoc]
  erw [hh]
  simp only [Functor.comp_obj, Iso.symm_inv, lowerStar_map_hom_app, Category.assoc,
    ← Functor.map_comp, ← op_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem section_support_restriction_reflect
    (Λ : Type (u + 1)) [CommRing Λ] {U X S : Scheme.{u}}
    (a : U ⟶ X) [Etale a]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (D : U.Etale)
    (p : D.left ⟶ S) [LocallyOfFiniteType p]
    (r : F.obj.obj (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale a)).obj D)))
    (t : ((a)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op D))
    (h : D ⟶ a.Etale.obj ((MorphismProperty.Over.map ⊤
      (inferInstance : Etale a)).obj D))
    (hh : h.left ≫ pullback.fst
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale a)).obj D).hom a = 𝟙 D.left)
    (ht : ((a)^*[ModuleCat.{u + 1} Λ].obj F).obj.map h.op
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).unit.app F).hom.app _ r) = t)
    (hs : SectionHasProperSupport Λ ((a)^*[ModuleCat.{u + 1} Λ].obj F) D p t) :
    SectionHasProperSupport Λ F
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale a)).obj D) p r := by
  obtain ⟨T, hT, hp⟩ := (sectionHasProperSupport_iff Λ _ D p t).1 hs
  apply (sectionHasProperSupport_iff Λ F _ p r).2
  refine ⟨T, ?_, hp⟩
  intro K _ _ k
  have hg := pullback_restrict_germ_zero Λ a F _ D h r k
  rw [ht] at hg
  have he : (k ≫ h.left) ≫ pullback.fst
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale a)).obj D).hom a = k := by
    rw [Category.assoc, hh]
    exact Category.comp_id k
  have hpoint (l : Spec (.of K) ⟶ D.left) (hl : l = k) :
      (pointSmallEtale (l ≫ ((MorphismProperty.Over.map ⊤
        (inferInstance : Etale a)).obj D).hom)).toPresheafFiber ((MorphismProperty.Over.map ⊤
        (inferInstance : Etale a)).obj D)
          (Over.homMk l) F.obj r = 0 ↔
      (pointSmallEtale (k ≫ ((MorphismProperty.Over.map ⊤
        (inferInstance : Etale a)).obj D).hom)).toPresheafFiber ((MorphismProperty.Over.map ⊤
        (inferInstance : Etale a)).obj D)
          (Over.homMk k) F.obj r = 0 := by
    subst l
    rfl
  exact (hT K k).trans ((not_congr hg).trans (not_congr (hpoint _ he)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem open_base_section_lift
    (Λ : Type (u + 1)) [CommRing Λ] {U B X Y : Scheme.{u}}
    (a : U ⟶ X) [IsOpenImmersion a] (e : B ⟶ Y) [IsOpenImmersion e]
    (g : U ⟶ B) [IsSeparated g] [LocallyOfFiniteType g]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    (sq : IsPullback a g f e)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : B.Etale)
    (t : ((a)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (g.Etale.obj V)))
    (ht : SectionHasProperSupport Λ ((a)^*[ModuleCat.{u + 1} Λ].obj F)
      (g.Etale.obj V) (pullback.fst V.hom g) t) :
    let VY := Scheme.Etale.mk (V.hom ≫ e)
    let D := g.Etale.obj V
    let W := f.Etale.obj VY
    ∃ (r : F.obj.obj (op W)) (h : D ⟶ a.Etale.obj W),
      SectionHasProperSupport Λ F W (pullback.fst VY.hom f) r ∧
      h.left ≫ pullback.fst W.hom a ≫ pullback.fst VY.hom f = pullback.fst V.hom g ∧
      ((a)^*[ModuleCat.{u + 1} Λ].obj F).obj.map h.op
        (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).unit.app F).hom.app
          (op W) r) = t := by
  dsimp only
  let A := ModuleCat.{u + 1} Λ
  let E := (a)^*[A].obj F
  let VY := Scheme.Etale.mk (V.hom ≫ e)
  let D := g.Etale.obj V
  let W := f.Etale.obj VY
  let D₀ := (MorphismProperty.Over.map ⊤ (inferInstance : Etale a)).obj D
  have sqD : IsPullback (pullback.fst V.hom g) (D.hom ≫ a) VY.hom f :=
    (IsPullback.of_hasPullback V.hom g).paste_vert sq.flip
  let c : D₀ ≅ W := MorphismProperty.Over.isoMk sqD.isoPullback
    sqD.isoPullback_hom_snd
  let h : D ⟶ a.Etale.obj W := MorphismProperty.Over.homMk
    (pullback.lift c.hom.left D.hom c.hom.w) (pullback.lift_snd _ _ _)
  let h₀ : D ⟶ a.Etale.obj D₀ := MorphismProperty.Over.homMk
    (pullback.lift (𝟙 D.left) D.hom (by simp [D₀])) (pullback.lift_snd _ _ _)
  let ρ := (upperStarIsoLocalizationRestriction A a inferInstance).app F
  let r₀ := ρ.hom.hom.app (op D) t
  let r := F.obj.map c.inv.op r₀
  have hrel (W : X.Etale) (h : D ⟶ a.Etale.obj W)
      (k : D₀ ⟶ W) (hk : h.left ≫ pullback.fst W.hom a = k.left) :
      ((upperStarLowerStarAdjunction A a).unit.app F).hom.app (op W) ≫
          E.obj.map h.op ≫ ρ.hom.hom.app (op D) = F.obj.map k.op := by
    have hh := localized_unit_restriction Λ a F W D h
    have he : ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ a inferInstance
      _root_.trivial).homEquiv D W).symm h = k := by
      apply MorphismProperty.Over.Hom.ext
      exact hk
    rw [he] at hh
    exact hh
  have hrt : E.obj.map h.op
      (((upperStarLowerStarAdjunction A a).unit.app F).hom.app (op W) r) = t := by
    apply ((ConcreteCategory.isIso_iff_bijective (ρ.hom.hom.app (op D))).1 inferInstance).1
    have hh := ConcreteCategory.congr_hom
      (hrel W h c.hom (pullback.lift_fst _ _ _)) r
    simp only [ConcreteCategory.comp_apply] at hh
    erw [hh]
    dsimp only [r]
    erw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      c.hom_inv_id, op_id, F.obj.map_id]
    rfl
  have hr₀ : SectionHasProperSupport Λ F D₀ (pullback.fst V.hom g) r₀ := by
    apply section_support_restriction_reflect Λ a F D (pullback.fst V.hom g) r₀ t h₀
      (pullback.lift_fst _ _ _)
    · apply ((ConcreteCategory.isIso_iff_bijective (ρ.hom.hom.app (op D))).1
        inferInstance).1
      have hh := ConcreteCategory.congr_hom
        (hrel D₀ h₀ (𝟙 D₀) (pullback.lift_fst _ _ _)) r₀
      simp only [ConcreteCategory.comp_apply] at hh
      erw [op_id, F.obj.map_id] at hh
      exact hh
    · exact ht
  have hc : c.hom.left ≫ pullback.fst VY.hom f = pullback.fst V.hom g :=
    sqD.isoPullback_hom_fst
  refine ⟨r, h, ?_, ?_, hrt⟩
  · apply (section_support_iso_iff Λ F c (pullback.fst V.hom g)
      (pullback.fst VY.hom f) hc r).1
    have hr : F.obj.map c.hom.op r = r₀ := by
      dsimp only [r]
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
        c.hom_inv_id, op_id, F.obj.map_id]
      rfl
    rwa [hr]
  · dsimp only [h]
    erw [pullback.lift_fst_assoc]
    exact hc

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem fibre_restriction_base_open
    (Λ : Type (u + 1)) [CommRing Λ] {U B X Y X' : Scheme.{u}}
    (a : U ⟶ X) (e : B ⟶ Y) [Etale e] (g : U ⟶ B) (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (yB : Spec (.of Ω) ⟶ B) (y : Spec (.of Ω) ⟶ Y) (hy : y = yB ≫ e)
    (b' : X' ⟶ U) (b : X' ⟶ X) (hb : b = b' ≫ a)
    (q : X' ⟶ Spec (.of Ω)) (sqB : CommSq b' q g yB) (sqY : CommSq b q f y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : B.Etale) (v : (pointSmallEtale yB).fiber.obj V)
    (h : g.Etale.obj V ⟶ a.Etale.obj (f.Etale.obj (Scheme.Etale.mk (V.hom ≫ e))))
    (hh : h.left ≫ pullback.fst
      (f.Etale.obj (Scheme.Etale.mk (V.hom ≫ e))).hom a ≫
        pullback.fst (V.hom ≫ e) f = pullback.fst V.hom g) :
    let A := ModuleCat.{u + 1} Λ
    let vY : (pointSmallEtale y).fiber.obj (Scheme.Etale.mk (V.hom ≫ e)) :=
      Over.homMk v.left (by
      change v.left ≫ (V.hom ≫ e) = y
      have hv : v.left ≫ V.hom = yB := v.w
      rw [← Category.assoc, hv, ← hy])
    geometricFibreSectionRestriction Λ sqY F _ vY ≫
        ((upperStarComp A b' a b hb).hom.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 X'))) =
      ((upperStarLowerStarAdjunction A a).unit.app F).hom.app
          (op (f.Etale.obj (Scheme.Etale.mk (V.hom ≫ e)))) ≫
        ((a)^*[A].obj F).obj.map h.op ≫
          geometricFibreSectionRestriction Λ sqB ((a)^*[A].obj F) V v := by
  dsimp only
  let A := ModuleCat.{u + 1} Λ
  let E := (a)^*[A].obj F
  let H := (b')^*[A].obj E
  let VY := Scheme.Etale.mk (V.hom ≫ e)
  let W := f.Etale.obj VY
  let D := g.Etale.obj V
  let vY : (pointSmallEtale y).fiber.obj VY :=
    Over.homMk v.left (by
      change v.left ≫ (V.hom ≫ e) = y
      have hv : v.left ≫ V.hom = yB := v.w
      rw [← Category.assoc, hv, ← hy])
  unfold geometricFibreSectionRestriction
  erw [section_composition_unit Λ b' a b hb F W _ (geometricFibreSectionLift sqY VY vY)]
  erw [reassoc_of% ((upperStarLowerStarAdjunction A b').unit.app E).hom.naturality h.op]
  congr 1
  congr 1
  change H.obj.map _ = H.obj.map (b'.Etale.map h).op ≫
    H.obj.map (geometricFibreSectionLift sqB V v).op
  rw [← Functor.map_comp, ← op_comp]
  congr 2
  apply MorphismProperty.Over.Hom.ext
  change (geometricFibreSectionLift sqY VY vY).left ≫
      ((MorphismProperty.Over.pullbackComp
        (P := @Etale) (Q := ⊤) b' a b hb).hom.app W).left =
    (geometricFibreSectionLift sqB V v).left ≫ (b'.Etale.map h).left
  dsimp only [geometricFibreSectionLift, Hom.Etale, D, W, VY,
    MorphismProperty.Over.pullback_obj_left, MorphismProperty.Over.pullback_obj_hom,
    MorphismProperty.Over.pullbackComp_hom_app_left,
    MorphismProperty.Over.pullback_map_left]
  have hw : h.left ≫ pullback.snd (pullback.snd (V.hom ≫ e) f) a =
      pullback.snd V.hom g := h.w
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simpa [geometricFibreSectionLift, Hom.Etale, Category.assoc, vY, D, W, VY] using
          (congrArg (fun z ↦
            ((geometricFibreSectionLift sqB V v).left ≫ pullback.fst D.hom b') ≫ z) hh).symm
      · simp [Category.assoc, pullback.condition, reassoc_of% hw, hb]
    · simp [Category.assoc, hw]
  · simp [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem general_fibre_section_lift
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (s : ((pullback.fst f y)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 (pullback f y)))))
    (hs : SectionHasProperSupport Λ ((pullback.fst f y)^*[ModuleCat.{u + 1} Λ].obj F)
      (Scheme.Etale.mk (𝟙 (pullback f y))) (pullback.snd f y) s) :
    ∃ (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V)
      (t : F.obj.obj (op (f.Etale.obj V))),
      SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) t ∧
      geometricFibreSectionRestriction Λ (IsPullback.of_hasPullback f y).toCommSq F V v t =
        s := by
  classical
  let A := ModuleCat.{u + 1} Λ
  obtain ⟨B, hB, hyB, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := y default) (U := ⊤) trivial
  have : IsAffine B := hB
  let e := B.ι
  let a := (f ⁻¹ᵁ B).ι
  let g := f ∣_ B
  have sq : IsPullback a g f e := (isPullback_morphismRestrict f B).flip
  have hyR : Set.range y ⊆ Set.range e := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z default]
    exact hyB
  let yB := IsOpenImmersion.lift e y hyR
  have hy : y = yB ≫ e := (IsOpenImmersion.lift_fac e y hyR).symm
  let b := pullback.fst f y
  let q := pullback.snd f y
  let sqY := IsPullback.of_hasPullback f y
  let bB := sq.lift b (q ≫ yB) (sqY.w.trans
    ((congrArg (fun z ↦ q ≫ z) hy).trans (Category.assoc q yB e).symm))
  have hb : b = bB ≫ a := (sq.lift_fst _ _ _).symm
  have sqB : IsPullback bB q g yB :=
    .of_right (by simpa only [← hb, ← hy] using sqY)
      (sq.lift_snd _ _ _) sq
  let S := (upperStarComp A bB a b hb).app F
  let E := (a)^*[A].obj F
  let sB := S.hom.hom.app (op (Scheme.Etale.mk (𝟙 (pullback f y)))) s
  have hsB : SectionHasProperSupport Λ ((bB)^*[A].obj E)
      (Scheme.Etale.mk (𝟙 (pullback f y))) q sB :=
    section_support_map Λ S.hom _ _ s hs
  obtain ⟨V, v, t, ht, hts⟩ := qcqs_fibre_section_lift Λ g yB bB q sqB E sB hsB
  obtain ⟨r, h, hr, hh, hrt⟩ := open_base_section_lift Λ a e g f sq F V t ht
  let VY := Scheme.Etale.mk (V.hom ≫ e)
  let vY : (pointSmallEtale y).fiber.obj VY :=
    Over.homMk v.left (by
      change v.left ≫ (V.hom ≫ e) = y
      have hv : v.left ≫ V.hom = yB := v.w
      rw [← Category.assoc, hv, ← hy])
  refine ⟨VY, vY, r, hr, ?_⟩
  apply ((ConcreteCategory.isIso_iff_bijective
    (S.hom.hom.app (op (Scheme.Etale.mk (𝟙 (pullback f y)))))).1 inferInstance).1
  have hcomp := ConcreteCategory.congr_hom
    (fibre_restriction_base_open Λ a e g f yB y hy bB b hb q
      sqB.toCommSq sqY.toCommSq F V v h hh) r
  simp only [ConcreteCategory.comp_apply] at hcomp
  erw [hrt] at hcomp
  exact hcomp.trans hts

/--
The restriction map on the geometric stalk is injective on a proper-support subsheaf, and
its range consists exactly of the properly supported fibre sections.  This is the geometric
content of Stacks Project, Tag 0F76: represent a stalk element on a pointed étale
neighbourhood, use the inverse-image germ formula to identify its fibre support, and use
extension by zero after shrinking and compactifying to lift every properly supported fibre
section.  The proof is deliberately separated from the elementary construction of the range
submodule and its canonical isomorphism.
Source: Stacks Project, Tag 0F76, support-image and extension-by-zero paragraphs.
(auxiliary; not a blueprint node).
-/
theorem properSupport_geometricStalk_image_core
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (i : G ⟶ (lowerStar (ModuleCat.{u + 1} Λ) f).obj F) (hi : Mono i)
    (hG : ∀ (V : Y.Etale) (s : F.obj.obj (op (f.Etale.obj V))),
      (∃ t, i.hom.app (op V) t = s) ↔
        SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) s)
    (c : lowerStar (ModuleCat.{u + 1} Λ) f ⋙ (Scheme.pointSmallEtale y).sheafFiber ⟶
      upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f y) ⋙
        (sheafSections (pullback f y).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (op (Scheme.Etale.mk (𝟙 (pullback f y)))))
    (hc : ∀ (V : Y.Etale) (v : (Scheme.pointSmallEtale y).fiber.obj V)
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (Scheme.pointSmallEtale y).toPresheafFiber V v
          ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ c.app F =
        geometricFibreSectionRestriction Λ (IsPullback.of_hasPullback f y).toCommSq F V v) :
    Function.Injective
        (((Scheme.pointSmallEtale y).sheafFiber.map i ≫ c.app F).hom) ∧
      ∀ s, s ∈ LinearMap.range
          (((Scheme.pointSmallEtale y).sheafFiber.map i ≫ c.app F).hom) ↔
        SectionHasProperSupport Λ
          ((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f y)).obj F)
          (Scheme.Etale.mk (𝟙 (pullback f y))) (pullback.snd f y) s := by
  refine ⟨properSupport_stalk_injective Λ f y F G i hi hG c hc, ?_⟩
  intro s
  constructor
  · rintro ⟨t, rfl⟩
    exact properSupport_stalk_range_subset Λ f y F G i hG c hc t
  · intro hs
    obtain ⟨V, v, t, ht, hst⟩ := general_fibre_section_lift Λ f y F s hs
    obtain ⟨z, hz⟩ := (hG V t).2 ht
    refine ⟨(pointSmallEtale y).toPresheafFiber V v G.obj z, ?_⟩
    change (c.app F) ((pointSmallEtale y).sheafFiber.map i
      ((pointSmallEtale y).toPresheafFiber V v G.obj z)) = s
    have hn := (pointSmallEtale y).toPresheafFiber_naturality_apply i.hom V v z
    change (pointSmallEtale y).sheafFiber.map i
      ((pointSmallEtale y).toPresheafFiber V v G.obj z) =
      (pointSmallEtale y).toPresheafFiber V v
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj (i.hom.app (op V) z) at hn
    rw [hn, hz]
    exact (ConcreteCategory.congr_hom (hc V v F) t).trans hst

end AlgebraicGeometry.Etale
