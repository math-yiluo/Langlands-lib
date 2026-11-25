/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import WeilConjectures.CategoryTheory.StageSystem.Pretriangulated
public import WeilConjectures.CategoryTheory.StageSystem.Restrict

/-!
# `t`-structures on the pair category of a triangulated stage system

Let `S` be a stage system of pretriangulated categories `C i` with triangulated transition
functors, and `t i` a `t`-structure on every stage such that the transition functors are
`t`-exact. Then the `2`-colimit `S.PairCategory` carries the induced `t`-structure
`CategoryTheory.StageSystem.tStructure`: an object `(i, x)` is `≤ n` (resp. `≥ n`) if `T_{m/i} x`
is `≤ n` (resp. `≥ n`) at some stage `m ≥ i`. The truncation triangles are the images of those of
the stages, and the orthogonality holds because a morphism is represented at a common stage where
both objects have the required degrees. Its heart consists of the objects lying eventually in the
hearts of the stages (`CategoryTheory.StageSystem.tStructure_heart`), so it is equivalent to the
`2`-colimit of the hearts (`CategoryTheory.StageSystem.restrictEquiv`).
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category Limits Pretriangulated Triangulated

namespace StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I] [Nonempty I] {C : I → Type u}
  [∀ i, Category.{v} (C i)] [∀ i, Preadditive (C i)] [∀ i, HasZeroObject (C i)]
  [∀ i, HasShift (C i) ℤ] [∀ i (n : ℤ), (shiftFunctor (C i) n).Additive]
  [∀ i, Pretriangulated (C i)] (S : StageSystem C)
  [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ] [∀ {i j : I} (h : i ≤ j), (S.T h).Additive]
  [∀ {i j : I} (h : i ≤ j), (S.T h).IsTriangulated]
  [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k), NatTrans.CommShift (S.assoc h h').hom ℤ]
  (t : ∀ i, TStructure (C i))
  (hle : ∀ {i j : I} (h : i ≤ j) (n : ℤ) (x : C i), (t i).le n x → (t j).le n ((S.T h).obj x))
  (hge : ∀ {i j : I} (h : i ≤ j) (n : ℤ) (x : C i), (t i).ge n x → (t j).ge n ((S.T h).obj x))

open PairCategory

/-- The `t`-structure on the pair category of a stage system of pretriangulated categories with
`t`-exact transition functors: `(i, x)` is `≤ n` (resp. `≥ n`) if `T_{m/i} x` is `≤ n`
(resp. `≥ n`) at some stage `m ≥ i`. -/
noncomputable def tStructure : TStructure S.PairCategory where
  le n := S.eventually fun i ↦ (t i).le n
  ge n := S.eventually fun i ↦ (t i).ge n
  le_isClosedUnderIsomorphisms n := eventually_isClosedUnderIsomorphisms (fun h ↦ hle h n)
  ge_isClosedUnderIsomorphisms n := eventually_isClosedUnderIsomorphisms (fun h ↦ hge h n)
  le_shift n a n' hn X := by
    rintro ⟨m, h, hX⟩
    refine ⟨m, h, ?_⟩
    change (t m).le n' ((S.T h).obj ((shiftFunctor (C X.stage) a).obj X.obj))
    exact ((t m).le n').prop_of_iso (((S.T h).commShiftIso a).app X.obj).symm
      ((t m).le_shift n a n' hn _ hX)
  ge_shift n a n' hn X := by
    rintro ⟨m, h, hX⟩
    refine ⟨m, h, ?_⟩
    change (t m).ge n' ((S.T h).obj ((shiftFunctor (C X.stage) a).obj X.obj))
    exact ((t m).ge n').prop_of_iso (((S.T h).commShiftIso a).app X.obj).symm
      ((t m).ge_shift n a n' hn _ hX)
  zero' {X Y} f := by
    rintro ⟨m, hm, hX⟩ ⟨m', hm', hY⟩
    obtain ⟨n, hn, hX', hY', u, rfl⟩ := exists_le_mkHom_eq f (commonStage m m')
    rw [← mkHom_zero hX' hY']
    congr 1
    exact (t n).zero' u
      (prop_toStage_of_le (fun h ↦ hle h 0) hX ((le_commonStage_left m m').trans hn))
      (prop_toStage_of_le (fun h ↦ hge h 1) hY ((le_commonStage_right m m').trans hn))
  le_zero_le X := fun ⟨m, h, hX⟩ ↦ ⟨m, h, (t m).le_zero_le _ hX⟩
  ge_one_le X := fun ⟨m, h, hX⟩ ↦ ⟨m, h, (t m).ge_one_le _ hX⟩
  exists_triangle_zero_one A := by
    obtain ⟨X, Y, hX, hY, f, g, h, hT⟩ := (t A.stage).exists_triangle_zero_one A.obj
    exact ⟨(S.ι A.stage).obj X, (S.ι A.stage).obj Y, ⟨A.stage, le_rfl, hle le_rfl 0 X hX⟩,
      ⟨A.stage, le_rfl, hge le_rfl 1 Y hY⟩, (S.ι _).map f, (S.ι _).map g,
      (S.ι _).map h ≫ ((S.ι _).commShiftIso (1 : ℤ)).hom.app X,
      (S.ι A.stage).map_distinguished _ hT⟩

lemma tStructure_le (n : ℤ) :
    (S.tStructure t hle hge).le n = S.eventually fun i ↦ (t i).le n := rfl

lemma tStructure_ge (n : ℤ) :
    (S.tStructure t hle hge).ge n = S.eventually fun i ↦ (t i).ge n := rfl

/-- The heart of the `t`-structure of the pair category consists of the objects lying eventually
in the hearts of the stages. -/
lemma tStructure_heart :
    (S.tStructure t hle hge).heart = S.eventually fun i ↦ (t i).heart :=
  (eventually_inf (fun h ↦ hle h 0) _ (fun h ↦ hge h 0)).symm

end StageSystem

end CategoryTheory
