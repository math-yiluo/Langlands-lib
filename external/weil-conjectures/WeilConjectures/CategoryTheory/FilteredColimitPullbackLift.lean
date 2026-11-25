/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! Intermediate finite-lifting statement for filtered category colimits. -/

@[expose] public section

universe u

open CategoryTheory.Limits

namespace CategoryTheory

private theorem cocone_obj_map
    {J : Type u} [SmallCategory J] (F : J ⥤ Cat.{u, u}) (V : Cocone F)
    {j k : J} (t : j ⟶ k) (X : F.obj j) :
    (V.ι.app k).toFunctor.obj ((F.map t).toFunctor.obj X) =
      (V.ι.app j).toFunctor.obj X := by
  exact congrArg (fun H : F.obj j ⟶ V.pt ↦ H.toFunctor.obj X) (V.w t)

private theorem cocone_arrow_map
    {J : Type u} [SmallCategory J] (F : J ⥤ Cat.{u, u}) (V : Cocone F)
    {j k : J} (t : j ⟶ k) (a : Arrow (F.obj j)) :
    (V.ι.app k).toFunctor.mapArrow.obj ((F.map t).toFunctor.mapArrow.obj a) =
      (V.ι.app j).toFunctor.mapArrow.obj a := by
  exact congrArg (fun H : F.obj j ⟶ V.pt ↦ H.toFunctor.mapArrow.obj a) (V.w t)

private theorem eventual_object_pair
    {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F) (hobjects : IsColimit (Cat.objects.mapCocone V))
    (j : J) (X₁ X₂ Y₁ Y₂ : F.obj j)
    (hx : (V.ι.app j).toFunctor.obj X₁ = (V.ι.app j).toFunctor.obj X₂)
    (hy : (V.ι.app j).toFunctor.obj Y₁ = (V.ι.app j).toFunctor.obj Y₂) :
    ∃ (k : J) (t : j ⟶ k),
      (F.map t).toFunctor.obj X₁ = (F.map t).toFunctor.obj X₂ ∧
      (F.map t).toFunctor.obj Y₁ = (F.map t).toFunctor.obj Y₂ := by
  obtain ⟨k, t, ht⟩ := (Types.FilteredColimit.isColimit_eq_iff' hobjects X₁ X₂).mp hx
  have hy' : (V.ι.app k).toFunctor.obj ((F.map t).toFunctor.obj Y₁) =
      (V.ι.app k).toFunctor.obj ((F.map t).toFunctor.obj Y₂) := by
    simpa only [cocone_obj_map] using hy
  obtain ⟨l, r, hr⟩ := (Types.FilteredColimit.isColimit_eq_iff' hobjects _ _).mp hy'
  change (F.map t).toFunctor.obj X₁ = (F.map t).toFunctor.obj X₂ at ht
  change (F.map r).toFunctor.obj ((F.map t).toFunctor.obj Y₁) =
    (F.map r).toFunctor.obj ((F.map t).toFunctor.obj Y₂) at hr
  refine ⟨l, t ≫ r, ?_, ?_⟩
  · simpa using congrArg (F.map r).toFunctor.obj ht
  · simpa using hr

private theorem lift_hom
    {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F) (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (j : J) (X Y : F.obj j)
    (a : (V.ι.app j).toFunctor.obj X ⟶ (V.ι.app j).toFunctor.obj Y) :
    ∃ (k : J) (t : j ⟶ k)
      (b : (F.map t).toFunctor.obj X ⟶ (F.map t).toFunctor.obj Y),
      Arrow.mk ((V.ι.app k).toFunctor.map b) = Arrow.mk a := by
  -- Represent the arrow, then align its endpoints at a common later stage.
  obtain ⟨i, b, hb⟩ := Types.jointly_surjective_of_isColimit harrows (Arrow.mk a)
  let k := IsFiltered.max j i
  let t := IsFiltered.leftToMax j i
  let r := IsFiltered.rightToMax j i
  let bk := (F.map r).toFunctor.mapArrow.obj b
  have hbk : (V.ι.app k).toFunctor.mapArrow.obj bk = Arrow.mk a :=
    (cocone_arrow_map F V r b).trans hb
  have hx : (V.ι.app k).toFunctor.obj bk.left =
      (V.ι.app k).toFunctor.obj ((F.map t).toFunctor.obj X) := by
    rw [cocone_obj_map]
    exact congrArg Arrow.left hbk
  have hy : (V.ι.app k).toFunctor.obj bk.right =
      (V.ι.app k).toFunctor.obj ((F.map t).toFunctor.obj Y) := by
    rw [cocone_obj_map]
    exact congrArg Arrow.right hbk
  obtain ⟨l, s, hsx, hsy⟩ := eventual_object_pair F V hobjects k
    bk.left ((F.map t).toFunctor.obj X) bk.right ((F.map t).toFunctor.obj Y) hx hy
  let bl := (F.map s).toFunctor.mapArrow.obj bk
  have ex : bl.left = (F.map (t ≫ s)).toFunctor.obj X := by
    simpa [bl] using hsx
  have ey : bl.right = (F.map (t ≫ s)).toFunctor.obj Y := by
    simpa [bl] using hsy
  refine ⟨l, t ≫ s, eqToHom ex.symm ≫ bl.hom ≫ eqToHom ey, ?_⟩
  simp only [Functor.map_comp, eqToHom_map, Arrow.arrow_mk_eqToHom_comp,
    Arrow.arrow_mk_comp_eqToHom]
  exact (cocone_arrow_map F V s bk).trans hbk

private theorem arrow_comp_congr
    {C : Type u} [Category.{u} C] {W X Y W' X' Y' : C}
    {a : W ⟶ X} {b : X ⟶ Y} {a' : W' ⟶ X'} {b' : X' ⟶ Y'}
    (ha : Arrow.mk a = Arrow.mk a') (hb : Arrow.mk b = Arrow.mk b') :
    Arrow.mk (a ≫ b) = Arrow.mk (a' ≫ b') := by
  obtain ⟨hx, hy, ha⟩ := (Arrow.mk_eq_mk_iff _ _).mp ha
  obtain ⟨hy', hz, hb⟩ := (Arrow.mk_eq_mk_iff _ _).mp hb
  subst W'
  subst X'
  subst Y'
  simpa using congrArg₂ (fun a b ↦ Arrow.mk (a ≫ b)) ha hb

/-- Existence of a mediating arrow for the image of a stable stage pullback.
Source: Stacks Project, Sites, Tag 09YL, pullback paragraph and Hom calculation.
(blueprint: lem-weil-pbc-filtered-colimit-pullback-exists)

Proof: Lift the vertex and two legs using joint surjectivity of the object and
arrow set colimits. Pass to a common stage above these representatives and j.
Successive applications of eventual equality in the object colimit identify
all endpoints with the transitioned cospan objects. Eventual equality in the
arrow colimit makes the cone equation hold after a further transition.
The pullback is preserved by the composite transition from j, so its limiting
cone supplies a mediating arrow at this stage. Apply the cocone functor; its
transition equations and preservation of composition give both factorization
equations in V.pt. No uniqueness assertion is used here. -/
theorem filteredColimit_pullback_exists
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (j : J) {X Y Z : F.obj j} (f : Y ⟶ X) (g : Z ⟶ X) [HasPullback f g]
    (hpres : ∀ (k : J) (a : j ⟶ k),
      PreservesLimit (cospan f g) (F.map a).toFunctor) :
    ∀ (W : V.pt) (a : W ⟶ (V.ι.app j).toFunctor.obj Y)
      (b : W ⟶ (V.ι.app j).toFunctor.obj Z),
      a ≫ (V.ι.app j).toFunctor.map f = b ≫ (V.ι.app j).toFunctor.map g →
      ∃ l : W ⟶ (V.ι.app j).toFunctor.obj (pullback f g),
        l ≫ (V.ι.app j).toFunctor.map (pullback.fst f g) = a ∧
        l ≫ (V.ι.app j).toFunctor.map (pullback.snd f g) = b := by
  classical
  intro W a b hab
  -- Represent the vertex above j and lift the two legs in succession.
  obtain ⟨i, W₀, hW₀⟩ := Types.jointly_surjective_of_isColimit hobjects W
  let k := IsFiltered.max j i
  let r := IsFiltered.leftToMax j i
  let r' := IsFiltered.rightToMax j i
  let R := (F.map r).toFunctor
  let Wk := (F.map r').toFunctor.obj W₀
  have hWk : (V.ι.app k).toFunctor.obj Wk = W :=
    (cocone_obj_map F V r' W₀).trans hW₀
  let a₀ : (V.ι.app k).toFunctor.obj Wk ⟶ (V.ι.app k).toFunctor.obj (R.obj Y) :=
    eqToHom hWk ≫ a ≫ eqToHom (cocone_obj_map F V r Y).symm
  have ha₀ : Arrow.mk a₀ = Arrow.mk a := by simp [a₀]
  obtain ⟨l, s, a₁, ha₁⟩ := lift_hom F V hobjects harrows k Wk (R.obj Y) a₀
  let S := (F.map s).toFunctor
  let Wl := S.obj Wk
  have hWl : (V.ι.app l).toFunctor.obj Wl = W :=
    (cocone_obj_map F V s Wk).trans hWk
  have hZl : (V.ι.app l).toFunctor.obj (S.obj (R.obj Z)) =
      (V.ι.app j).toFunctor.obj Z :=
    (cocone_obj_map F V s (R.obj Z)).trans (cocone_obj_map F V r Z)
  let b₀ : (V.ι.app l).toFunctor.obj Wl ⟶
      (V.ι.app l).toFunctor.obj (S.obj (R.obj Z)) :=
    eqToHom hWl ≫ b ≫ eqToHom hZl.symm
  have hb₀ : Arrow.mk b₀ = Arrow.mk b := by simp [b₀]
  obtain ⟨m, t, b₁, hb₁⟩ := lift_hom F V hobjects harrows l Wl (S.obj (R.obj Z)) b₀
  let T := (F.map t).toFunctor
  let am := T.map a₁
  let fm := T.map (S.map (R.map f))
  let gm := T.map (S.map (R.map g))
  have ham : Arrow.mk ((V.ι.app m).toFunctor.map am) = Arrow.mk a :=
    (cocone_arrow_map F V t (Arrow.mk a₁)).trans (ha₁.trans ha₀)
  have hbm : Arrow.mk ((V.ι.app m).toFunctor.map b₁) = Arrow.mk b := hb₁.trans hb₀
  have hfm : Arrow.mk ((V.ι.app m).toFunctor.map fm) =
      Arrow.mk ((V.ι.app j).toFunctor.map f) :=
    (cocone_arrow_map F V t (Arrow.mk (S.map (R.map f)))).trans
      ((cocone_arrow_map F V s (Arrow.mk (R.map f))).trans
        (cocone_arrow_map F V r (Arrow.mk f)))
  have hgm : Arrow.mk ((V.ι.app m).toFunctor.map gm) =
      Arrow.mk ((V.ι.app j).toFunctor.map g) :=
    (cocone_arrow_map F V t (Arrow.mk (S.map (R.map g)))).trans
      ((cocone_arrow_map F V s (Arrow.mk (R.map g))).trans
        (cocone_arrow_map F V r (Arrow.mk g)))
  -- Equality of the two composites in the apex becomes equality at a later stage.
  have heq : (V.ι.app m).toFunctor.mapArrow.obj (Arrow.mk (am ≫ fm)) =
      (V.ι.app m).toFunctor.mapArrow.obj (Arrow.mk (b₁ ≫ gm)) := by
    simp only [Functor.mapArrow_obj, Arrow.mk_hom, Functor.map_comp]
    exact (arrow_comp_congr ham hfm).trans
      ((congrArg Arrow.mk hab).trans (arrow_comp_congr hbm hgm).symm)
  obtain ⟨n, v, hv⟩ := (Types.FilteredColimit.isColimit_eq_iff' harrows _ _).mp heq
  change Arrow.mk ((F.map v).toFunctor.map (am ≫ fm)) =
    Arrow.mk ((F.map v).toFunctor.map (b₁ ≫ gm)) at hv
  have hv' := (Arrow.mk_inj _ _).mp hv
  rw [Functor.map_comp, Functor.map_comp] at hv'
  -- The composite transition preserves the original pullback.
  let Q := (F.map v).toFunctor
  let H := R ⋙ S ⋙ T ⋙ Q
  have : PreservesLimit (cospan f g) H := by
    simpa only [F.map_comp, Cat.Hom.comp_toFunctor] using hpres n (r ≫ s ≫ t ≫ v)
  let hp := isLimitOfHasPullbackOfPreservesLimit H f g
  let c := PullbackCone.IsLimit.lift hp (Q.map am) (Q.map b₁) hv'
  have hc₁ : c ≫ H.map (pullback.fst f g) = Q.map am :=
    PullbackCone.IsLimit.lift_fst hp _ _ hv'
  have hc₂ : c ≫ H.map (pullback.snd f g) = Q.map b₁ :=
    PullbackCone.IsLimit.lift_snd hp _ _ hv'
  -- Map its mediator into the apex and transport the endpoints along cocone equations.
  have hWn : (V.ι.app n).toFunctor.obj (Q.obj (T.obj Wl)) = W :=
    (cocone_obj_map F V v (T.obj Wl)).trans
      ((cocone_obj_map F V t Wl).trans hWl)
  have hPn : (V.ι.app n).toFunctor.obj (H.obj (pullback f g)) =
      (V.ι.app j).toFunctor.obj (pullback f g) := by
    exact (cocone_obj_map F V v _).trans ((cocone_obj_map F V t _).trans
      ((cocone_obj_map F V s _).trans (cocone_obj_map F V r _)))
  have hH (d : Arrow (F.obj j)) :
      (V.ι.app n).toFunctor.mapArrow.obj (H.mapArrow.obj d) =
        (V.ι.app j).toFunctor.mapArrow.obj d := by
    exact (cocone_arrow_map F V v _).trans ((cocone_arrow_map F V t _).trans
      ((cocone_arrow_map F V s _).trans (cocone_arrow_map F V r d)))
  let cn := (V.ι.app n).toFunctor.map c
  refine ⟨eqToHom hWn.symm ≫ cn ≫ eqToHom hPn, ?_, ?_⟩
  · apply (Arrow.mk_inj _ _).mp
    have hl : Arrow.mk (eqToHom hWn.symm ≫ cn ≫ eqToHom hPn) = Arrow.mk cn := by
      simp
    have he : Arrow.mk (cn ≫ (V.ι.app n).toFunctor.map (H.map (pullback.fst f g))) =
        Arrow.mk ((V.ι.app n).toFunctor.map (Q.map am)) := by
      simp only [cn, ← Functor.map_comp, hc₁]
    exact (arrow_comp_congr hl (hH (Arrow.mk (pullback.fst f g))).symm).trans
      (he.trans ((cocone_arrow_map F V v (Arrow.mk am)).trans ham))
  · apply (Arrow.mk_inj _ _).mp
    have hl : Arrow.mk (eqToHom hWn.symm ≫ cn ≫ eqToHom hPn) = Arrow.mk cn := by
      simp
    have he : Arrow.mk (cn ≫ (V.ι.app n).toFunctor.map (H.map (pullback.snd f g))) =
        Arrow.mk ((V.ι.app n).toFunctor.map (Q.map b₁)) := by
      simp only [cn, ← Functor.map_comp, hc₂]
    exact (arrow_comp_congr hl (hH (Arrow.mk (pullback.snd f g))).symm).trans
      (he.trans ((cocone_arrow_map F V v (Arrow.mk b₁)).trans hbm))

end CategoryTheory
