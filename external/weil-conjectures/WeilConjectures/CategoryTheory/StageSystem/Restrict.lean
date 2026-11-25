/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Restriction of a stage system to object properties preserved by the transitions

Let `S` be a stage system on categories `C i` and `P i` object properties of the stages which are
preserved by the transition functors. The transition functors and the associators restrict to the
full subcategories, giving a stage system `S.restrict P hP` on the categories
`(P i).FullSubcategory`. An object `(i, x)` of the pair category of `S` *eventually* satisfies
`P` (`CategoryTheory.StageSystem.eventually`) if `T_{n/i} x` satisfies `P n` at some stage
`n ≥ i`. The inclusions of the full subcategories induce a fully faithful functor between the
pair categories, whose essential image consists of the objects eventually satisfying `P`; hence
the pair category of the restricted system, the `2`-colimit of the full subcategories, is
equivalent to the full subcategory of the `2`-colimit on the objects eventually satisfying `P`
(`CategoryTheory.StageSystem.restrictEquiv`).

In the application, `P E` is the constructible heart of `D^b_c(Y, E)` and this identifies the heart
of `D^b_c(Y, ℚ̄_ℓ) = 2-colim_E D^b_c(Y, E)` with the `2`-colimit of the hearts.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category

namespace StageSystem

variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  (S : StageSystem C) (P : ∀ i, ObjectProperty (C i))
  (hP : ∀ {i j : I} (h : i ≤ j) (x : C i), P i x → P j ((S.T h).obj x))

/-- The restriction of a stage system to object properties `P i` of the stages which are
preserved by the transition functors: the stage system of the full subcategories
`(P i).FullSubcategory`, with the restricted transition functors and associators. -/
def restrict : StageSystem (fun i ↦ (P i).FullSubcategory) where
  T h := (P _).liftFullSubcategory (P _) (S.T h) (hP h)
  assoc h h' := NatIso.ofComponents (fun x ↦ (P _).isoMk ((S.assoc h h').app x.obj))
    (fun f ↦ (P _).hom_ext ((S.assoc h h').hom.naturality f.hom))
  cocycle h h' h'' x := (P _).hom_ext (S.cocycle h h' h'' x.obj)

/-- The inclusions of the full subcategories, as a morphism of stage systems
`S.restrict P hP ⟶ S`. -/
def restrictMorphism : Morphism (S.restrict P hP) S where
  Φ i := (P i).ι
  β _ := Iso.refl _
  coh h h' x := by
    simp [restrict]

include hP in
variable {S P} in
/-- If `T_{n/i} x` satisfies `P n`, then so does `T_{r/i} x` for every stage `r ≥ n`. -/
lemma prop_toStage_of_le [∀ i, (P i).IsClosedUnderIsomorphisms] {X : S.PairCategory} {n r : I}
    {h : X.stage ≤ n} (hX : P n (X.toStage h)) (hnr : n ≤ r) :
    P r (X.toStage (h.trans hnr)) :=
  (P r).prop_of_iso ((S.assoc h hnr).app X.obj) (hP hnr _ hX)

open PairCategory

variable [IsDirectedOrder I]

/-- An object `(i, x)` of the pair category *eventually satisfies* `P` if `T_{n/i} x` satisfies
`P n` at some stage `n ≥ i`. -/
def eventually : ObjectProperty S.PairCategory :=
  fun X : S.PairCategory ↦ ∃ (n : I) (h : X.stage ≤ n), P n (X.toStage h)

variable {S} in
/-- An isomorphism of the pair category is represented by an isomorphism at some stage. -/
lemma exists_iso_toStage {X Y : S.PairCategory} (e : X ≅ Y) :
    ∃ (n : I) (hX : X.stage ≤ n) (hY : Y.stage ≤ n), Nonempty (X.toStage hX ≅ Y.toStage hY) := by
  obtain ⟨n, -, hX, hY, hY', hX', u, v, hu, hv⟩ := exists_common_stage e.hom e.inv X.stage
  have h₁ : mkHom n hX hX (u ≫ v) = mkHom n hX hX (𝟙 _) := by
    rw [← mkHom_comp_mkHom, ← hu, ← hv, e.hom_inv_id, id_eq_mkHom]
  have h₂ : mkHom n hY hY (v ≫ u) = mkHom n hY hY (𝟙 _) := by
    rw [← mkHom_comp_mkHom, ← hu, ← hv, e.inv_hom_id, id_eq_mkHom]
  obtain ⟨p, hp, e₁⟩ := (mkHom_eq_mkHom_iff _ _).1 h₁
  obtain ⟨q, hq, e₂⟩ := (mkHom_eq_mkHom_iff _ _).1 h₂
  obtain ⟨r, hpr, hqr⟩ := exists_ge_ge p q
  have k₁ : S.tr (hp.trans hpr) (u ≫ v) = 𝟙 _ := by
    rw [← tr_tr hp hpr, (tr_injective hp).2 e₁, tr_tr, tr_id]
  have k₂ : S.tr (hq.trans hqr) (v ≫ u) = 𝟙 _ := by
    rw [← tr_tr hq hqr, (tr_injective hq).2 e₂, tr_tr, tr_id]
  exact ⟨r, hX.trans (hp.trans hpr), hY.trans (hp.trans hpr),
    ⟨{ hom := S.tr (hp.trans hpr) u
       inv := S.tr (hp.trans hpr) v
       hom_inv_id := by rw [← tr_comp, k₁]
       inv_hom_id := by rw [← tr_comp, k₂] }⟩⟩

include hP in
variable {S P} in
/-- The property of eventually satisfying `P` is closed under isomorphisms of the pair
category. -/
lemma eventually_isClosedUnderIsomorphisms [∀ i, (P i).IsClosedUnderIsomorphisms] :
    (S.eventually P).IsClosedUnderIsomorphisms where
  of_iso {X Y} e := by
    rintro ⟨n, h, hX⟩
    obtain ⟨m, hX', hY', ⟨e'⟩⟩ := exists_iso_toStage e
    obtain ⟨r, hnr, hmr⟩ := exists_ge_ge n m
    refine ⟨r, hY'.trans hmr, (P r).prop_of_iso ?_ (prop_toStage_of_le hP hX hnr)⟩
    exact ((S.assoc hX' hmr).app X.obj).symm ≪≫ (S.T hmr).mapIso e' ≪≫
      (S.assoc hY' hmr).app Y.obj

include hP in
variable {S P} in
/-- Eventually satisfying `P i ⊓ Q i` is eventually satisfying `P` and eventually satisfying
`Q`. -/
lemma eventually_inf (Q : ∀ i, ObjectProperty (C i))
    (hQ : ∀ {i j : I} (h : i ≤ j) (x : C i), Q i x → Q j ((S.T h).obj x))
    [∀ i, (P i).IsClosedUnderIsomorphisms] [∀ i, (Q i).IsClosedUnderIsomorphisms] :
    S.eventually (fun i ↦ P i ⊓ Q i) = S.eventually P ⊓ S.eventually Q := by
  ext X
  refine ⟨fun ⟨n, h, hP', hQ'⟩ ↦ ⟨⟨n, h, hP'⟩, ⟨n, h, hQ'⟩⟩, ?_⟩
  rintro ⟨⟨n, h, hP'⟩, ⟨m, h', hQ'⟩⟩
  obtain ⟨r, hnr, hmr⟩ := exists_ge_ge n m
  exact ⟨r, h.trans hnr, prop_toStage_of_le hP hP' hnr, prop_toStage_of_le hQ hQ' hmr⟩

/-- The functor `2-colim_i (P i).FullSubcategory ⥤ 2-colim_i C i` induced by the inclusions of
the full subcategories. -/
noncomputable def restrictFunctor : (S.restrict P hP).PairCategory ⥤ S.PairCategory :=
  (S.restrictMorphism P hP).functor

lemma restrictFunctor_obj (X : (S.restrict P hP).PairCategory) :
    (S.restrictFunctor P hP).obj X = ⟨X.stage, X.obj.obj⟩ := rfl

lemma restrictFunctor_map_mkHom {X Y : (S.restrict P hP).PairCategory} {n : I}
    (hX : X.stage ≤ n) (hY : Y.stage ≤ n) (u : X.toStage hX ⟶ Y.toStage hY) :
    (S.restrictFunctor P hP).map (mkHom n hX hY u) =
      mkHom (X := (S.restrictFunctor P hP).obj X) (Y := (S.restrictFunctor P hP).obj Y)
        n hX hY u.hom := by
  change mkHom (X := (S.restrictFunctor P hP).obj X) (Y := (S.restrictFunctor P hP).obj Y) n hX hY
    ((S.restrictMorphism P hP).mapAt u) = _
  congr 1
  exact (Category.id_comp _).trans (Category.comp_id _)

instance : (S.restrictFunctor P hP).Faithful where
  map_injective {X Y} := by
    intro f g
    obtain ⟨n, -, hX, hY, -, -, u, u', rfl, rfl⟩ := exists_common_stage f g X.stage
    intro e
    rw [restrictFunctor_map_mkHom, restrictFunctor_map_mkHom, mkHom_eq_mkHom_iff] at e
    obtain ⟨p, h, e₁⟩ := e
    exact (mkHom_eq_mkHom_iff _ _).2 ⟨p, h, (P p).hom_ext e₁⟩

instance : (S.restrictFunctor P hP).Full where
  map_surjective {X Y} f := by
    induction f using hom_induction with
    | h n hX hY u =>
      exact ⟨mkHom n hX hY ((P n).homMk (X := X.toStage hX) (Y := Y.toStage hY) u),
        by rw [restrictFunctor_map_mkHom]; rfl⟩

lemma restrictFunctor_obj_eventually (X : (S.restrict P hP).PairCategory) :
    S.eventually P ((S.restrictFunctor P hP).obj X) :=
  ⟨X.stage, le_rfl, hP le_rfl _ X.obj.property⟩

/-- The essential image of `2-colim_i (P i).FullSubcategory ⥤ 2-colim_i C i` consists of the
objects eventually satisfying `P`. -/
lemma essImage_restrictFunctor [∀ i, (P i).IsClosedUnderIsomorphisms] :
    (S.restrictFunctor P hP).essImage = S.eventually P := by
  ext Y
  constructor
  · rintro ⟨X, ⟨e⟩⟩
    exact (eventually_isClosedUnderIsomorphisms hP).of_iso e
      (S.restrictFunctor_obj_eventually P hP X)
  · rintro ⟨n, h, hY⟩
    exact ⟨⟨n, ⟨Y.toStage h, hY⟩⟩, ⟨(S.isoToStage Y h).symm⟩⟩

/-- The functor `2-colim_i (P i).FullSubcategory ⥤ (2-colim_i C i)`, corestricted to the objects
eventually satisfying `P`. -/
noncomputable def restrictFunctorEventually :
    (S.restrict P hP).PairCategory ⥤ (S.eventually P).FullSubcategory :=
  (S.eventually P).lift (S.restrictFunctor P hP) (S.restrictFunctor_obj_eventually P hP)

instance : (S.restrictFunctorEventually P hP).EssSurj where
  mem_essImage Y := by
    obtain ⟨n, h, hY⟩ := Y.property
    exact ⟨⟨n, ⟨Y.obj.toStage h, hY⟩⟩, ⟨(S.eventually P).isoMk (S.isoToStage Y.obj h).symm⟩⟩

instance : (S.restrictFunctorEventually P hP).IsEquivalence where
  faithful := by dsimp only [restrictFunctorEventually]; infer_instance
  full := by dsimp only [restrictFunctorEventually]; infer_instance

/-- The `2`-colimit of the full subcategories `(P i).FullSubcategory` is equivalent to the full
subcategory of the `2`-colimit `S.PairCategory` on the objects eventually satisfying `P`. -/
noncomputable def restrictEquiv :
    (S.restrict P hP).PairCategory ≌ (S.eventually P).FullSubcategory :=
  (S.restrictFunctorEventually P hP).asEquivalence

end StageSystem

end CategoryTheory
