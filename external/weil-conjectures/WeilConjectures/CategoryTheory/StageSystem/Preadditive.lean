/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# The pair category of a system of preadditive categories is preadditive

If the categories `C i` of a stage system are preadditive and the transition functors are additive,
the Hom sets of the pair category, being filtered colimits of abelian groups, are abelian groups:
addition, zero and negatives are computed after transport to a common stage, and these common-stage
operations are independent of the representatives. The stage inclusions and the functors induced by
additive morphisms of stage systems are additive, and the pair category has a zero object as soon as
the stages do.

## Main statements

- `CategoryTheory.StageSystem.PairCategory.preadditive`: the pair category is preadditive.
- `CategoryTheory.StageSystem.PairCategory.hasZeroObject`: it has a zero object.
- `CategoryTheory.StageSystem.PairCategory.isZero_iff`: an object `(i, x)` is zero if and only if
  `T x` is zero at some stage.
-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory

open Category Limits

namespace StageSystem

variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  {S : StageSystem C} [∀ i, Preadditive (C i)] [∀ (i j : I) (h : i ≤ j), (S.T h).Additive]

@[simp]
lemma tr_add {i j n p : I} {hi : i ≤ n} {hj : j ≤ n} (h : n ≤ p) {x : C i} {y : C j}
    (f g : (S.T hi).obj x ⟶ (S.T hj).obj y) :
    S.tr h (f + g) = S.tr h f + S.tr h g := by
  simp [tr]

@[simp]
lemma tr_neg {i j n p : I} {hi : i ≤ n} {hj : j ≤ n} (h : n ≤ p) {x : C i} {y : C j}
    (f : (S.T hi).obj x ⟶ (S.T hj).obj y) :
    S.tr h (-f) = -S.tr h f := by
  simp [tr]

@[simp]
lemma tr_zero {i j n p : I} {hi : i ≤ n} {hj : j ≤ n} (h : n ≤ p) {x : C i} {y : C j} :
    S.tr h (0 : (S.T hi).obj x ⟶ (S.T hj).obj y) = 0 := by
  simp [tr]

namespace PairCategory

variable [IsDirectedOrder I]

/-- The sum of two representatives, computed at a common stage. -/
noncomputable def Rep.add {X Y : S.PairCategory} (r s : Rep X Y) : Rep X Y :=
  ⟨commonStage r.k s.k, r.hX.trans (le_commonStage_left _ _),
    r.hY.trans (le_commonStage_left _ _),
    S.tr (le_commonStage_left _ _) r.u + S.tr (le_commonStage_right _ _) s.u⟩

lemma Rep.add_rel {X Y : S.PairCategory} {r r' s s' : Rep X Y}
    (hr : Rep.Rel r r') (hs : Rep.Rel s s') : Rep.Rel (r.add s) (r'.add s') := by
  obtain ⟨p, h₁, h₂, e⟩ := hr
  obtain ⟨q, h₃, h₄, e'⟩ := hs
  obtain ⟨a, ha₁, ha₂⟩ := exists_ge_ge p q
  obtain ⟨b, hb₁, hb₂⟩ := exists_ge_ge (commonStage r.k s.k) (commonStage r'.k s'.k)
  obtain ⟨m, hm₁, hm₂⟩ := exists_ge_ge a b
  refine ⟨m, hb₁.trans hm₂, hb₂.trans hm₂, ?_⟩
  change S.tr _ (S.tr _ r.u + S.tr _ s.u) = S.tr _ (S.tr _ r'.u + S.tr _ s'.u)
  rw [tr_add, tr_add, tr_tr, tr_tr, tr_tr, tr_tr]
  have E := rel_of_eq h₁ h₂ e (ha₁.trans hm₁)
  have E' := rel_of_eq h₃ h₄ e' (ha₂.trans hm₁)
  exact congr_arg₂ (· + ·) E E'

noncomputable instance (X Y : S.PairCategory) : Add (X ⟶ Y) where
  add f g := Quotient.map₂ (sa := Rep.setoid X Y) (sb := Rep.setoid X Y)
    (sc := Rep.setoid X Y) Rep.add (fun _ _ hr _ _ hs ↦ Rep.add_rel hr hs) f g

noncomputable instance (X Y : S.PairCategory) : Neg (X ⟶ Y) where
  neg f := Quotient.map (sa := Rep.setoid X Y) (sb := Rep.setoid X Y)
    (fun r ↦ ⟨r.k, r.hX, r.hY, -r.u⟩)
    (fun _ _ ⟨p, hr, hs, e⟩ ↦ ⟨p, hr, hs, by
      change S.tr _ (-_) = S.tr _ (-_)
      rw [tr_neg, tr_neg, e]⟩) f

noncomputable instance (X Y : S.PairCategory) : Zero (X ⟶ Y) where
  zero := mkHom (commonStage X.stage Y.stage) (le_commonStage_left _ _)
    (le_commonStage_right _ _) 0

lemma mkHom_add {X Y : S.PairCategory} {n : I} {hX : X.stage ≤ n} {hY : Y.stage ≤ n}
    (u v : X.toStage hX ⟶ Y.toStage hY) :
    mkHom n hX hY u + mkHom n hX hY v = mkHom n hX hY (u + v) := by
  change mkHom _ _ _ _ = _
  rw [mkHom_eq_mkHom_iff']
  refine ⟨commonStage n n, le_rfl, le_commonStage_left _ _, ?_⟩
  simp only [tr_add, tr_tr]

lemma mkHom_neg {X Y : S.PairCategory} {n : I} {hX : X.stage ≤ n} {hY : Y.stage ≤ n}
    (u : X.toStage hX ⟶ Y.toStage hY) :
    -mkHom n hX hY u = mkHom n hX hY (-u) := rfl

lemma mkHom_zero {X Y : S.PairCategory} {n : I} (hX : X.stage ≤ n) (hY : Y.stage ≤ n) :
    mkHom n hX hY 0 = (0 : X ⟶ Y) := by
  change _ = mkHom _ _ _ _
  rw [mkHom_eq_mkHom_iff']
  obtain ⟨p, h, h'⟩ := exists_ge_ge n (commonStage X.stage Y.stage)
  exact ⟨p, h, h', by simp⟩

omit [∀ i, Preadditive (C i)] [∀ (i j : I) (h : i ≤ j), (S.T h).Additive] in
/-- Lift three morphisms with the same source and target to a common stage. -/
lemma exists_common_stage₃ {X Y : S.PairCategory} (f g k : X ⟶ Y) :
    ∃ (n : I) (hX : X.stage ≤ n) (hY : Y.stage ≤ n) (u v w : X.toStage hX ⟶ Y.toStage hY),
      f = mkHom n hX hY u ∧ g = mkHom n hX hY v ∧ k = mkHom n hX hY w := by
  obtain ⟨n₁, -, hX₁, hY₁, u, rfl⟩ := exists_le_mkHom_eq f X.stage
  obtain ⟨n₂, h₂, hX₂, hY₂, v, rfl⟩ := exists_le_mkHom_eq g n₁
  obtain ⟨n₃, h₃, hX₃, hY₃, w, rfl⟩ := exists_le_mkHom_eq k n₂
  exact ⟨n₃, hX₃, hY₃, S.tr (h₂.trans h₃) u, S.tr h₃ v, w, (mkHom_tr _ _).symm,
    (mkHom_tr _ _).symm, rfl⟩

noncomputable instance (X Y : S.PairCategory) : AddCommGroup (X ⟶ Y) where
  add_assoc f g k := by
    obtain ⟨n, hX, hY, u, v, w, rfl, rfl, rfl⟩ := exists_common_stage₃ f g k
    simp only [mkHom_add, add_assoc]
  zero_add f := by
    induction f using hom_induction with
    | h n hX hY u => rw [← mkHom_zero hX hY, mkHom_add, zero_add]
  add_zero f := by
    induction f using hom_induction with
    | h n hX hY u => rw [← mkHom_zero hX hY, mkHom_add, add_zero]
  add_comm f g := by
    obtain ⟨n, hX, hY, u, v, -, rfl, rfl, -⟩ := exists_common_stage₃ f g f
    simp only [mkHom_add, add_comm]
  neg_add_cancel f := by
    induction f using hom_induction with
    | h n hX hY u => rw [mkHom_neg, mkHom_add, neg_add_cancel, mkHom_zero]
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The pair category of a system of preadditive categories with additive transition functors is
preadditive. -/
noncomputable instance preadditive : Preadditive S.PairCategory where
  add_comp X Y Z f f' g := by
    obtain ⟨n, -, hX, hY, -, -, u, -, rfl, -⟩ := exists_common_stage f f X.stage
    obtain ⟨n', hn, hX', hY', -, -, u', -, rfl, -⟩ := exists_common_stage f' f' n
    obtain ⟨n'', hn', hY'', hZ, -, -, w, -, rfl, -⟩ := exists_common_stage g g n'
    rw [← mkHom_tr (hn.trans hn') u, ← mkHom_tr hn' u', mkHom_add, mkHom_comp_mkHom,
      mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_add, Preadditive.add_comp]
  comp_add X Y Z f g g' := by
    obtain ⟨n, -, hX, hY, -, -, u, -, rfl, -⟩ := exists_common_stage f f X.stage
    obtain ⟨n', hn, hY', hZ, -, -, w, -, rfl, -⟩ := exists_common_stage g g n
    obtain ⟨n'', hn', hY'', hZ', -, -, w', -, rfl, -⟩ := exists_common_stage g' g' n'
    rw [← mkHom_tr (hn.trans hn') u, ← mkHom_tr hn' w, mkHom_add, mkHom_comp_mkHom,
      mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_add, Preadditive.comp_add]

/-- An object `(i, x)` of the pair category is zero if and only if `T x` is zero at some stage. -/
lemma isZero_iff (X : S.PairCategory) :
    IsZero X ↔ ∃ (n : I) (h : X.stage ≤ n), IsZero (X.toStage h) := by
  rw [IsZero.iff_id_eq_zero, id_eq_mkHom X le_rfl, ← mkHom_zero le_rfl le_rfl,
    mkHom_eq_mkHom_iff]
  constructor
  · rintro ⟨p, h, e⟩
    refine ⟨p, le_rfl.trans h, ?_⟩
    have : IsZero ((S.T h).obj (X.toStage le_rfl)) := by
      rw [IsZero.iff_id_eq_zero, ← Functor.map_id, e, Functor.map_zero]
    exact this.of_iso ((S.assoc le_rfl h).app X.obj).symm
  · rintro ⟨n, h, hz⟩
    refine ⟨n, h, ?_⟩
    have : IsZero ((S.T h).obj (X.toStage le_rfl)) := hz.of_iso ((S.assoc le_rfl h).app X.obj)
    exact this.eq_of_src _ _

lemma isZero_of_isZero_toStage (X : S.PairCategory) {n : I} (h : X.stage ≤ n)
    (hz : IsZero (X.toStage h)) : IsZero X :=
  (isZero_iff X).2 ⟨n, h, hz⟩

lemma isZero_ι_obj {i : I} {x : C i} (hx : IsZero x) : IsZero ((S.ι i).obj x) :=
  isZero_of_isZero_toStage ⟨i, x⟩ le_rfl (Functor.map_isZero _ hx)

open ZeroObject in
/-- The pair category has a zero object as soon as the stages do. -/
lemma hasZeroObject [Nonempty I] [∀ i, HasZeroObject (C i)] : HasZeroObject S.PairCategory :=
  ⟨⟨(S.ι (Classical.arbitrary I)).obj 0, isZero_ι_obj (isZero_zero _)⟩⟩

end PairCategory

open PairCategory

variable [IsDirectedOrder I]

instance (i : I) : (S.ι i).Additive where
  map_add {x y f g} := by
    rw [ι_map_eq le_rfl, ι_map_eq le_rfl, ι_map_eq le_rfl, Functor.map_add, mkHom_add]

namespace Morphism

variable {D : I → Type u'} [∀ i, Category.{v'} (D i)] [∀ i, Preadditive (D i)]
  {S' : StageSystem D} [∀ (i j : I) (h : i ≤ j), (S'.T h).Additive] (F : Morphism S S')

omit [∀ (i j : I) (h : i ≤ j), (S.T h).Additive] [IsDirectedOrder I]
  [∀ (i j : I) (h : i ≤ j), (S'.T h).Additive] in
@[simp]
lemma mapAt_add [∀ i, (F.Φ i).Additive] {i j n : I} {hi : i ≤ n} {hj : j ≤ n} {x : C i}
    {y : C j} (u v : (S.T hi).obj x ⟶ (S.T hj).obj y) :
    F.mapAt (u + v) = F.mapAt u + F.mapAt v := by
  simp [mapAt]

instance [∀ i, (F.Φ i).Additive] : F.functor.Additive where
  map_add {X Y f g} := by
    obtain ⟨n, hX, hY, u, v, -, rfl, rfl, -⟩ := exists_common_stage₃ f g f
    rw [mkHom_add, functor_map_mkHom, functor_map_mkHom, functor_map_mkHom, mapAt_add,
      mkHom_add]

end Morphism

end StageSystem

end CategoryTheory
