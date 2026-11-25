/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicTopology.SemiSimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Truncated semi-simplicial objects and their coskeletal extensions

An `N`-truncated semi-simplicial object `T` (`CategoryTheory.SemiSimplicialObject.Truncated`)
has objects `T.obj n` and face maps `T.δ n i : T.obj (n + 1) ⟶ T.obj n` for `n < N`, satisfying
the simplicial identities whenever they make sense; the objects `T.obj n` for `n > N` play no
role.

In a category with finite limits, `T` extends to a semi-simplicial object `T.cosk`, its
*coskeletal extension*: it agrees with `T` in degrees `≤ N`
(`CategoryTheory.SemiSimplicialObject.Truncated.coskIso`,
`CategoryTheory.SemiSimplicialObject.Truncated.cosk_δ`), and above degree `N` the
`(n + 1)`-simplices are the matching object of the `n`-simplices, so that every compatible
family `Fin (n + 2) → (W ⟶ T.cosk.obj n)`, `n ≥ N`, is the boundary of a unique
`(n + 1)`-simplex (`CategoryTheory.SemiSimplicialObject.Truncated.cosk_hasUniqueLifts`). This is
the non-recursive coskeleton `(cosk_N T)_n = lim_{faces of Δⁿ of dimension ≤ N} T`, built one
degree at a time.

A morphism into a semi-simplicial object `W` with unique lifts above degree `N` is determined
by its components in degrees `≤ N`, and every family of such components commuting with the face
maps extends (`CategoryTheory.SemiSimplicialObject.extendHom`). The property of having unique
lifts in degree `n` is preserved by functors preserving finite limits
(`CategoryTheory.SemiSimplicialObject.HasUniqueLifts.map`).
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits

namespace CategoryTheory.SemiSimplicialObject

variable {C : Type u} [Category.{v} C]

section Lifts

variable (U : SemiSimplicialObject C)

/-- `U` has *lifts in degree `n`*: every compatible family `Fin (n + 2) → (W ⟶ U.obj n)` is the
boundary of an `(n + 1)`-simplex `W ⟶ U.obj (n + 1)`. -/
def HasLifts (n : ℕ) : Prop :=
  ∀ ⦃W : C⦄ (x : Fin (n + 2) → (W ⟶ U.obj n)), U.Compatible x →
    ∃ y : W ⟶ U.obj (n + 1), ∀ i, y ≫ U.δ n i = x i

/-- `U` has *unique lifts in degree `n`*: every compatible family `Fin (n + 2) → (W ⟶ U.obj n)`
is the boundary of a unique `(n + 1)`-simplex, i.e. the matching map in degree `n` is an
isomorphism. -/
structure HasUniqueLifts (n : ℕ) : Prop where
  hasLifts : U.HasLifts n
  ext ⦃W : C⦄ (y y' : W ⟶ U.obj (n + 1)) : (∀ i, y ≫ U.δ n i = y' ≫ U.δ n i) → y = y'

variable [HasFiniteLimits C]

lemma HasUniqueLifts.isIso_toMatching {n : ℕ} (h : U.HasUniqueLifts n) :
    IsIso (U.toMatching n) := by
  obtain ⟨y, hy⟩ := h.hasLifts (U.matchingπ n) (U.compatible_matchingπ n)
  refine ⟨y, h.ext _ _ fun i ↦ ?_, U.matching_hom_ext fun i ↦ ?_⟩
  · simp [hy]
  · simp [hy]

lemma hasUniqueLifts_of_isIso_toMatching {n : ℕ} [IsIso (U.toMatching n)] :
    U.HasUniqueLifts n where
  hasLifts W x hx := ⟨U.matchingLift x hx ≫ inv (U.toMatching n), fun i ↦ by
    rw [Category.assoc, ← U.toMatching_π n i, IsIso.inv_hom_id_assoc, matchingLift_π]⟩
  ext W y y' h := by
    rw [← cancel_mono (U.toMatching n)]
    exact U.matching_hom_ext fun i ↦ by simpa using h i

end Lifts

section Preserves

variable {D : Type u'} [Category.{v'} D] [HasFiniteLimits C]
  (G : C ⥤ D) [PreservesFiniteLimits G] (U : SemiSimplicialObject C)

/-- A functor preserving finite limits sends matching objects to matching objects: compatible
families with values in the image of `U` lift uniquely to the image of the matching object. -/
lemma map_matching_existsUnique (n : ℕ) {W : D} (x : Fin (n + 2) → (W ⟶ G.obj (U.obj n)))
    (hx : (U.map G).Compatible x) :
    ∃! y : W ⟶ G.obj (U.matching n), ∀ i, y ≫ G.map (U.matchingπ n i) = x i := by
  cases n with
  | zero =>
    let hP := isLimitFanMkObjOfIsLimit G _ _ (productIsProduct fun _ : Fin 2 ↦ U.obj 0)
    refine ⟨hP.lift (Fan.mk W x), fun i ↦ hP.fac (Fan.mk W x) ⟨i⟩, fun y hy ↦ ?_⟩
    refine Fan.IsLimit.hom_ext hP _ _ fun i ↦ ?_
    exact (hy i).trans (hP.fac (Fan.mk W x) ⟨i⟩).symm
  | succ m =>
    let hP := isLimitFanMkObjOfIsLimit G _ _ (productIsProduct fun _ : Fin (m + 3) ↦ U.obj (m + 1))
    let hQ := isLimitFanMkObjOfIsLimit G _ _ (productIsProduct fun _ : MatchingIndex m ↦ U.obj m)
    let hE := isLimitForkMapOfIsLimit G _ (equalizerIsEqualizer (U.matchingLeft m)
      (U.matchingRight m))
    let k : W ⟶ G.obj (∏ᶜ fun _ : Fin (m + 3) ↦ U.obj (m + 1)) := hP.lift (Fan.mk W x)
    have hk (i : Fin (m + 3)) : k ≫ G.map (Pi.π _ i) = x i := hP.fac (Fan.mk W x) ⟨i⟩
    have hkk : k ≫ G.map (U.matchingLeft m) = k ≫ G.map (U.matchingRight m) := by
      refine Fan.IsLimit.hom_ext hQ _ _ fun p ↦ ?_
      change (k ≫ G.map (U.matchingLeft m)) ≫ G.map (Pi.π _ p) =
        (k ≫ G.map (U.matchingRight m)) ≫ G.map (Pi.π _ p)
      simp only [Category.assoc, ← G.map_comp, matchingLeft, matchingRight, Pi.lift_comp_π]
      rw [G.map_comp, G.map_comp, reassoc_of% hk, reassoc_of% hk]
      exact hx p.1.1 p.1.2 p.2
    obtain ⟨l, hl⟩ := Fork.IsLimit.lift' hE k hkk
    have hl' : l ≫ G.map (equalizer.ι _ _) = k := hl
    refine ⟨l, fun i ↦ ?_, fun y hy ↦ ?_⟩
    · change l ≫ G.map (equalizer.ι _ _ ≫ Pi.π _ i) = x i
      rw [G.map_comp, reassoc_of% hl']
      exact hk i
    · refine Fork.IsLimit.hom_ext hE ?_
      change y ≫ G.map (equalizer.ι _ _) = l ≫ G.map (equalizer.ι _ _)
      rw [hl']
      refine Fan.IsLimit.hom_ext hP _ _ fun i ↦ ?_
      change (y ≫ G.map (equalizer.ι _ _)) ≫ G.map (Pi.π _ i) = k ≫ G.map (Pi.π _ i)
      rw [hk, Category.assoc, ← G.map_comp]
      exact hy i

/-- Unique lifts are preserved by functors preserving finite limits. -/
lemma HasUniqueLifts.map {n : ℕ} (h : U.HasUniqueLifts n) : (U.map G).HasUniqueLifts n := by
  have := h.isIso_toMatching
  refine ⟨fun W x hx ↦ ?_, fun W y y' hyy' ↦ ?_⟩
  · obtain ⟨y, hy, -⟩ := U.map_matching_existsUnique G n x hx
    refine ⟨y ≫ G.map (inv (U.toMatching n)), fun i ↦ ?_⟩
    simp only [map_δ, Category.assoc, ← G.map_comp, ← hy i]
    congr 2
    rw [← U.toMatching_π n i, IsIso.inv_hom_id_assoc]
  · have e : y ≫ G.map (U.toMatching n) = y' ≫ G.map (U.toMatching n) := by
      obtain ⟨z, -, hz⟩ := U.map_matching_existsUnique G n (fun i ↦ y' ≫ G.map (U.δ n i))
        (by simpa using (U.map G).compatible_δ y')
      refine (hz _ fun i ↦ ?_).trans (hz _ fun i ↦ ?_).symm
      · simpa [← G.map_comp] using hyy' i
      · simp [← G.map_comp]
    simpa using congrArg (· ≫ G.map (inv (U.toMatching n))) e

omit [PreservesFiniteLimits G] in
/-- The comparison map from the image of the matching object of `U` to the matching object of
the image of `U`. It is an isomorphism (`isIso_mapMatchingComparison`). -/
noncomputable def mapMatchingComparison (n : ℕ) [HasFiniteLimits D] :
    G.obj (U.matching n) ⟶ (U.map G).matching n :=
  (U.map G).matchingLift (fun i ↦ G.map (U.matchingπ n i)) (by
    cases n with
    | zero => trivial
    | succ m =>
      intro i j hij
      simp only [map_δ, ← G.map_comp]
      exact congrArg G.map (U.compatible_matchingπ (m + 1) i j hij))

omit [PreservesFiniteLimits G] in
@[reassoc (attr := simp)]
lemma mapMatchingComparison_π (n : ℕ) [HasFiniteLimits D] (i : Fin (n + 2)) :
    U.mapMatchingComparison G n ≫ (U.map G).matchingπ n i = G.map (U.matchingπ n i) := by
  simp [mapMatchingComparison]

omit [PreservesFiniteLimits G] in
@[reassoc (attr := simp)]
lemma map_toMatching_comp_mapMatchingComparison (n : ℕ) [HasFiniteLimits D] :
    G.map (U.toMatching n) ≫ U.mapMatchingComparison G n = (U.map G).toMatching n :=
  (U.map G).matching_hom_ext fun i ↦ by simp [← G.map_comp]

instance isIso_mapMatchingComparison (n : ℕ) [HasFiniteLimits D] :
    IsIso (U.mapMatchingComparison G n) := by
  obtain ⟨y, hy, -⟩ := U.map_matching_existsUnique G n ((U.map G).matchingπ n)
    ((U.map G).compatible_matchingπ n)
  refine ⟨y, ?_, (U.map G).matching_hom_ext fun i ↦ by simp [hy]⟩
  obtain ⟨z, -, hz⟩ := U.map_matching_existsUnique G n (fun i ↦ G.map (U.matchingπ n i))
    (by simpa using (U.map G).compatible_matchingπ n |>.comp _ (U.mapMatchingComparison G n))
  exact (hz _ fun i ↦ by simp [hy]).trans (hz _ fun i ↦ by simp).symm
end Preserves

section MatchingMap

variable [HasFiniteLimits C] {U V : SemiSimplicialObject C} (f : U ⟶ V)

/-- The map of matching objects induced by a morphism of semi-simplicial objects. -/
noncomputable def matchingMap (n : ℕ) : U.matching n ⟶ V.matching n :=
  V.matchingLift (fun i ↦ U.matchingπ n i ≫ f.app n) ((U.compatible_matchingπ n).map _ f)

@[reassoc (attr := simp)]
lemma matchingMap_π (n : ℕ) (i : Fin (n + 2)) :
    matchingMap f n ≫ V.matchingπ n i = U.matchingπ n i ≫ f.app n := by
  simp [matchingMap]

@[reassoc]
lemma toMatching_matchingMap (n : ℕ) :
    U.toMatching n ≫ matchingMap f n = f.app (n + 1) ≫ V.toMatching n :=
  V.matching_hom_ext fun i ↦ by simp

/-- The map of matching objects in degree `n` is an isomorphism if `f` is an isomorphism in
degrees `≤ n`. -/
lemma isIso_matchingMap (n : ℕ) (hf : ∀ k, k ≤ n → IsIso (f.app k)) :
    IsIso (matchingMap f n) := by
  have := hf n le_rfl
  have hc : U.Compatible (fun i ↦ V.matchingπ n i ≫ inv (f.app n)) := by
    cases n with
    | zero => trivial
    | succ m =>
      have := hf m (by omega)
      have h (i : Fin (m + 2)) : inv (f.app (m + 1)) ≫ U.δ m i = V.δ m i ≫ inv (f.app m) := by
        rw [IsIso.eq_comp_inv, Category.assoc, ← Hom.app_δ, IsIso.inv_hom_id_assoc]
      intro i j hij
      simp only [Category.assoc, h]
      simpa only [Category.assoc] using (V.compatible_matchingπ (m + 1) i j hij) =≫ inv (f.app m)
  exact ⟨U.matchingLift _ hc, U.matching_hom_ext fun i ↦ by simp,
    V.matching_hom_ext fun i ↦ by simp⟩

end MatchingMap

section Extend

variable {U W : SemiSimplicialObject C} (N : ℕ) (hW : ∀ n, N ≤ n → W.HasLifts n)
  (f : ∀ n, n ≤ N → (U.obj n ⟶ W.obj n))
  (hf : ∀ n (h : n < N) (i : Fin (n + 2)), f (n + 1) h ≫ W.δ n i = U.δ n i ≫ f n h.le)

/-- (Implementation) The next component of `CategoryTheory.SemiSimplicialObject.extendHom`. -/
noncomputable def extendStep (n : ℕ) (g : U.obj n ⟶ W.obj n)
    (hg : W.Compatible fun i ↦ U.δ n i ≫ g) : U.obj (n + 1) ⟶ W.obj (n + 1) :=
  if h : n + 1 ≤ N then f (n + 1) h else (hW n (by omega) _ hg).choose

include hf in
lemma extendStep_δ (n : ℕ) (g : U.obj n ⟶ W.obj n) (hg : W.Compatible fun i ↦ U.δ n i ≫ g)
    (hgf : ∀ h : n ≤ N, g = f n h) (i : Fin (n + 2)) :
    extendStep N hW f n g hg ≫ W.δ n i = U.δ n i ≫ g := by
  rw [extendStep]
  split_ifs with h
  · rw [hf n h i, hgf]
  · exact (hW n (by omega) _ hg).choose_spec i

/-- (Implementation) The components of `CategoryTheory.SemiSimplicialObject.extendHom` in
degrees `n` and `n + 1`. -/
noncomputable def extendAux : (n : ℕ) →
    {g : (U.obj n ⟶ W.obj n) × (U.obj (n + 1) ⟶ W.obj (n + 1)) //
      (∀ i, g.2 ≫ W.δ n i = U.δ n i ≫ g.1) ∧ (∀ h : n ≤ N, g.1 = f n h) ∧
        ∀ h : n + 1 ≤ N, g.2 = f (n + 1) h}
  | 0 => ⟨(f 0 (Nat.zero_le _), extendStep N hW f 0 (f 0 (Nat.zero_le _)) trivial),
      extendStep_δ N hW f hf 0 (f 0 (Nat.zero_le _)) trivial (fun _ ↦ rfl), fun _ ↦ rfl,
      fun h ↦ by rw [extendStep, dite_eq_left h]⟩
  | n + 1 =>
    let a := extendAux n
    have hg : W.Compatible fun i ↦ U.δ (n + 1) i ≫ a.1.2 := by
      intro i j hij
      rw [Category.assoc, Category.assoc, a.2.1, a.2.1, U.δ_comp_δ_assoc n hij]
    ⟨(a.1.2, extendStep N hW f (n + 1) a.1.2 hg),
      extendStep_δ N hW f hf (n + 1) _ hg a.2.2.2, a.2.2.2,
      fun h ↦ by rw [extendStep, dite_eq_left h]⟩

/-- A morphism `U ⟶ W` into a semi-simplicial object with lifts above degree `N`, extending
components in degrees `≤ N` which commute with the face maps. -/
noncomputable def extendHom : U ⟶ W where
  app n := (extendAux N hW f hf n).1.1
  app_δ n i := (extendAux N hW f hf n).2.1 i

lemma extendHom_app (n : ℕ) (h : n ≤ N) : (extendHom N hW f hf).app n = f n h :=
  (extendAux N hW f hf n).2.2.1 h

end Extend

section Truncated

/-- An `N`-truncated semi-simplicial object: objects `obj n` for `n ≤ N` and face maps
`δ n i : obj (n + 1) ⟶ obj n` for `n < N`, satisfying the simplicial identities. -/
structure Truncated (C : Type u) [Category.{v} C] (N : ℕ) where
  /-- The object of `n`-simplices, for `n ≤ N`. -/
  obj (n : ℕ) (hn : n ≤ N) : C
  /-- The `i`-th face map from `(n + 1)`-simplices to `n`-simplices, for `n < N`. -/
  δ (n : ℕ) (hn : n < N) (i : Fin (n + 2)) : obj (n + 1) hn ⟶ obj n hn.le
  /-- The simplicial identities. -/
  δ_comp_δ (n : ℕ) (hn : n + 1 < N) {i j : Fin (n + 2)} (h : i ≤ j) :
    δ (n + 1) hn j.succ ≫ δ n (by omega) i = δ (n + 1) hn i.castSucc ≫ δ n (by omega) j

variable {N : ℕ}

/-- The `N`-truncation of a semi-simplicial object. -/
@[simps]
def truncate (U : SemiSimplicialObject C) (N : ℕ) : Truncated C N where
  obj n _ := U.obj n
  δ n _ := U.δ n
  δ_comp_δ n _ _ _ h := U.δ_comp_δ n h

namespace Truncated

/-- The image of a truncated semi-simplicial object under a functor. -/
@[simps]
def map {D : Type u'} [Category.{v'} D] (G : C ⥤ D) (T : Truncated C N) : Truncated D N where
  obj n h := G.obj (T.obj n h)
  δ n h i := G.map (T.δ n h i)
  δ_comp_δ n hn _ _ h := by simp only [← G.map_comp, T.δ_comp_δ n hn h]

/-- (Implementation) The data `(n`-simplices, `(n + 1)`-simplices, face maps`)` of a
semi-simplicial object in degrees `n` and `n + 1`, used to build the coskeletal extension one
degree at a time. -/
structure Window (C : Type u) [Category.{v} C] (n : ℕ) where
  /-- The `n`-simplices. -/
  lower : C
  /-- The `(n + 1)`-simplices. -/
  upper : C
  /-- The face maps. -/
  face : Fin (n + 2) → (upper ⟶ lower)

variable [HasFiniteLimits C]

/-- (Implementation) The two maps `∏ᵢ upper ⟶ ∏_{i ≤ j} lower` whose equalizer is the matching
object of a window. -/
noncomputable def Window.left {n : ℕ} (w : Window C n) :
    ∏ᶜ (fun _ : Fin (n + 3) ↦ w.upper) ⟶ ∏ᶜ (fun _ : MatchingIndex n ↦ w.lower) :=
  Pi.lift fun p ↦ Pi.π _ p.1.2.succ ≫ w.face p.1.1

/-- (Implementation) The two maps `∏ᵢ upper ⟶ ∏_{i ≤ j} lower` whose equalizer is the matching
object of a window. -/
noncomputable def Window.right {n : ℕ} (w : Window C n) :
    ∏ᶜ (fun _ : Fin (n + 3) ↦ w.upper) ⟶ ∏ᶜ (fun _ : MatchingIndex n ↦ w.lower) :=
  Pi.lift fun p ↦ Pi.π _ p.1.1.castSucc ≫ w.face p.1.2

/-- (Implementation) The next window: the new simplices are the matching object. -/
noncomputable def Window.next {n : ℕ} (w : Window C n) : Window C (n + 1) where
  lower := w.upper
  upper := equalizer w.left w.right
  face i := equalizer.ι _ _ ≫ Pi.π _ i

/-- (Implementation) The window in degree `0` whose `1`-simplices are pairs of `0`-simplices. -/
noncomputable def Window.zero (X : C) : Window C 0 where
  lower := X
  upper := ∏ᶜ fun _ : Fin 2 ↦ X
  face i := Pi.π _ i

lemma Window.next_face_comp {n : ℕ} (w : Window C n) {i j : Fin (n + 2)} (h : i ≤ j) :
    w.next.face j.succ ≫ w.face i = w.next.face i.castSucc ≫ w.face j := by
  have := congrArg (· ≫ Pi.π (fun _ : MatchingIndex n ↦ w.lower) ⟨(i, j), h⟩)
    (equalizer.condition w.left w.right)
  simpa [Window.left, Window.right, Window.next] using this

/-- Compatible families into `w.upper` lift uniquely to the next window. -/
lemma Window.next_existsUnique {n : ℕ} (w : Window C n) {W : C}
    (x : Fin (n + 3) → (W ⟶ w.upper))
    (hx : ∀ i j : Fin (n + 2), i ≤ j → x j.succ ≫ w.face i = x i.castSucc ≫ w.face j) :
    ∃! y : W ⟶ w.next.upper, ∀ i, y ≫ w.next.face i = x i := by
  have hl : Pi.lift x ≫ w.left = Pi.lift x ≫ w.right := by
    ext p
    simpa [Window.left, Window.right] using hx p.1.1 p.1.2 p.2
  refine ⟨equalizer.lift (Pi.lift x) hl, fun i ↦ by simp [Window.next], fun y hy ↦ ?_⟩
  apply equalizer.hom_ext
  ext i
  simpa [Window.next] using hy i

lemma Window.zero_existsUnique (X : C) {W : C} (x : Fin 2 → (W ⟶ X)) :
    ∃! y : W ⟶ (Window.zero X).upper, ∀ i, y ≫ (Window.zero X).face i = x i :=
  ⟨Pi.lift x, fun i ↦ by simp [Window.zero],
    fun y hy ↦ Pi.hom_ext _ _ fun i ↦ by simpa [Window.zero] using hy i⟩

/-- (Implementation) The windows of the coskeletal extension. -/
noncomputable def window (T : Truncated C N) : (n : ℕ) → Window C n
  | 0 => if h : 0 < N then ⟨T.obj 0 h.le, T.obj 1 h, T.δ 0 h⟩
      else Window.zero (T.obj 0 (Nat.zero_le _))
  | n + 1 => if h : n + 1 < N then ⟨T.obj (n + 1) h.le, T.obj (n + 2) h, T.δ (n + 1) h⟩
      else (window T n).next

variable (T : Truncated C N)

lemma window_of_lt {n : ℕ} (h : n < N) :
    T.window n = ⟨T.obj n h.le, T.obj (n + 1) h, T.δ n h⟩ := by
  cases n with
  | zero => rw [window, dite_eq_left h]
  | succ n => rw [window, dite_eq_left h]

lemma window_succ_of_le {n : ℕ} (h : N ≤ n + 1) : T.window (n + 1) = (T.window n).next := by
  rw [window, dite_eq_right (by omega)]

lemma window_zero_of_eq (h : N = 0) : T.window 0 = Window.zero (T.obj 0 (Nat.zero_le _)) := by
  rw [window, dite_eq_right (by omega)]

lemma window_lower_succ (n : ℕ) : (T.window (n + 1)).lower = (T.window n).upper := by
  by_cases h : n + 1 < N
  · rw [T.window_of_lt h, T.window_of_lt (by omega : n < N)]
  · rw [T.window_succ_of_le (by omega)]
    rfl

lemma window_lower (n : ℕ) (h : n ≤ N) : (T.window n).lower = T.obj n h := by
  cases n with
  | zero =>
    by_cases h0 : 0 < N
    · rw [T.window_of_lt h0]
    · rw [T.window_zero_of_eq (by omega)]
      rfl
  | succ n => rw [T.window_lower_succ, T.window_of_lt (by omega : n < N)]

/-- The coskeletal extension of an `N`-truncated semi-simplicial object: it agrees with `T` in
degrees `≤ N`, and above degree `N` the `(n + 1)`-simplices are the matching object of the
`n`-simplices. -/
noncomputable def cosk : SemiSimplicialObject C where
  obj n := (T.window n).lower
  δ n i := eqToHom (T.window_lower_succ n) ≫ (T.window n).face i
  δ_comp_δ n {i j} h := by
    simp only [Category.assoc]
    congr 1
    by_cases hn : n + 1 < N
    · have key : ∀ (w₁ : Window C (n + 1)) (_ : w₁ = ⟨T.obj (n + 1) hn.le, T.obj (n + 2) hn,
          T.δ (n + 1) hn⟩) (w₀ : Window C n)
          (_ : w₀ = ⟨T.obj n (by omega), T.obj (n + 1) (by omega), T.δ n (by omega)⟩)
          (e : w₁.lower = w₀.upper),
          w₁.face j.succ ≫ eqToHom e ≫ w₀.face i = w₁.face i.castSucc ≫ eqToHom e ≫ w₀.face j := by
        rintro _ rfl _ rfl e
        simpa using T.δ_comp_δ n hn h
      exact key _ (T.window_of_lt hn) _ (T.window_of_lt (by omega)) _
    · have key : ∀ (w₁ : Window C (n + 1)) (_ : w₁ = (T.window n).next)
          (e : w₁.lower = (T.window n).upper),
          w₁.face j.succ ≫ eqToHom e ≫ (T.window n).face i =
            w₁.face i.castSucc ≫ eqToHom e ≫ (T.window n).face j := by
        rintro _ rfl e
        simpa using (T.window n).next_face_comp h
      exact key _ (T.window_succ_of_le (by omega)) _

/-- The coskeletal extension agrees with `T` in degrees `≤ N`. -/
noncomputable def coskIso (n : ℕ) (h : n ≤ N) : T.cosk.obj n ≅ T.obj n h :=
  eqToIso (T.window_lower n h)

lemma cosk_δ (n : ℕ) (h : n < N) (i : Fin (n + 2)) :
    T.cosk.δ n i = (T.coskIso (n + 1) h).hom ≫ T.δ n h i ≫ (T.coskIso n h.le).inv := by
  have key : ∀ (w : Window C n) (_ : w = ⟨T.obj n h.le, T.obj (n + 1) h, T.δ n h⟩)
      (e : (T.window (n + 1)).lower = w.upper) (e' : w.lower = T.obj n h.le),
      eqToHom e ≫ w.face i = eqToHom (T.window_lower (n + 1) h) ≫ T.δ n h i ≫ eqToHom e'.symm := by
    rintro _ rfl e e'
    simp
  exact key _ (T.window_of_lt h) (T.window_lower_succ n) (T.window_lower n h.le)

/-- Above degree `N`, compatible families lift uniquely in the coskeletal extension. -/
lemma cosk_hasUniqueLifts (n : ℕ) (h : N ≤ n) : T.cosk.HasUniqueLifts n := by
  -- the faces of `T.cosk` out of degree `n + 1` are those of the window `n`
  suffices H : ∀ {W : C} (x : Fin (n + 2) → (W ⟶ (T.window n).lower)),
      T.cosk.Compatible x → ∃! y : W ⟶ (T.window n).upper, ∀ i, y ≫ (T.window n).face i = x i by
    refine ⟨fun W x hx ↦ ?_, fun W y y' hyy' ↦ ?_⟩
    · obtain ⟨y, hy, -⟩ := H x hx
      exact ⟨y ≫ eqToHom (T.window_lower_succ n).symm, fun i ↦ by simpa [cosk] using hy i⟩
    · have := (H _ (T.cosk.compatible_δ y')).unique
        (y₁ := y ≫ eqToHom (T.window_lower_succ n))
        (y₂ := y' ≫ eqToHom (T.window_lower_succ n))
        (fun i ↦ by simpa [cosk] using hyy' i) (fun i ↦ by simp [cosk])
      exact (cancel_mono _).1 this
  intro W x hx
  cases n with
  | zero =>
    have key : ∀ (w : Window C 0) (_ : w = Window.zero (T.obj 0 (Nat.zero_le _)))
        (x : Fin 2 → (W ⟶ w.lower)), ∃! y : W ⟶ w.upper, ∀ i, y ≫ w.face i = x i := by
      rintro _ rfl x
      exact Window.zero_existsUnique _ x
    exact key _ (T.window_zero_of_eq (by omega)) x
  | succ m =>
    -- the compatibility of `x` is relative to the faces of the window `m`
    have hx' : ∀ i j : Fin (m + 2), i ≤ j →
        (x j.succ ≫ eqToHom (T.window_lower_succ m)) ≫ (T.window m).face i =
          (x i.castSucc ≫ eqToHom (T.window_lower_succ m)) ≫ (T.window m).face j := by
      intro i j hij
      simpa [cosk] using hx i j hij
    have key : ∀ (w : Window C (m + 1)) (_ : w = (T.window m).next)
        (e : w.lower = (T.window m).upper) (x : Fin (m + 3) → (W ⟶ w.lower)),
        (∀ i j : Fin (m + 2), i ≤ j → (x j.succ ≫ eqToHom e) ≫ (T.window m).face i =
          (x i.castSucc ≫ eqToHom e) ≫ (T.window m).face j) →
        ∃! y : W ⟶ w.upper, ∀ i, y ≫ w.face i = x i := by
      rintro _ rfl e x hx
      simpa using (T.window m).next_existsUnique x (by simpa using hx)
    exact key _ (T.window_succ_of_le (by omega)) _ x hx'

lemma cosk_hasLifts (n : ℕ) (h : N ≤ n) : T.cosk.HasLifts n :=
  (T.cosk_hasUniqueLifts n h).hasLifts

section Map

variable {D : Type u'} [Category.{v'} D] [HasFiniteLimits D] (G : C ⥤ D) [PreservesFiniteLimits G]

/-- The comparison morphism from the coskeletal extension of the image of `T` under a functor
preserving finite limits to the image of the coskeletal extension of `T`. It is an isomorphism
in degrees `≤ N` (`CategoryTheory.SemiSimplicialObject.Truncated.isIso_coskMapHom_app`), and in
fact in all degrees. -/
noncomputable def coskMapHom : (T.map G).cosk ⟶ T.cosk.map G :=
  extendHom N (fun n h ↦ ((T.cosk_hasUniqueLifts n h).map G).hasLifts)
    (fun n h ↦ ((T.map G).coskIso n h).hom ≫ G.map (T.coskIso n h).inv) (fun n h i ↦ by
      change _ ≫ G.map (T.cosk.δ n i) = _
      rw [T.cosk_δ n h, (T.map G).cosk_δ n h]
      simp [G.map_comp])

lemma coskMapHom_app (n : ℕ) (h : n ≤ N) :
    (T.coskMapHom G).app n = ((T.map G).coskIso n h).hom ≫ G.map (T.coskIso n h).inv :=
  extendHom_app _ _ _ _ n h

lemma isIso_coskMapHom_app (n : ℕ) (h : n ≤ N) : IsIso ((T.coskMapHom G).app n) := by
  rw [coskMapHom_app _ _ n h]
  infer_instance

end Map

end Truncated

end Truncated

end CategoryTheory.SemiSimplicialObject
