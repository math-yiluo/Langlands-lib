/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.SiteCechComplex
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SiteCechComplex

variable {C : Type u} [Category.{v} C] {T : Type v} {U : C}
  {f : T → C} {hom : ∀ t, f t ⟶ U} (S : SiteCechComplex f hom)

/-- The coproduct of representables on the degree-p products, as a presheaf of sets.
Source: Stacks 03AT (blueprint: lem-weil-pbc-site-cech-free-complex-exact). -/
def tuplePresheaf (p : ℕ) : Cᵒᵖ ⥤ Type v where
  obj X := Σ t : Fin (p + 1) → T, X.unop ⟶ S.W p t
  map g := ↾fun x ↦ ⟨x.1, g.unop ≫ x.2⟩
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨x.1, (𝟙 X.unop) ≫ x.2⟩ :
      Σ t : Fin (p + 1) → T, X.unop ⟶ S.W p t) = x
    rw [Category.id_comp]
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨x.1, (h.unop ≫ g.unop) ≫ x.2⟩ :
      Σ t : Fin (p + 1) → T, _ ⟶ S.W p t) = ⟨x.1, h.unop ≫ (g.unop ≫ x.2)⟩
    rw [Category.assoc]

/-- A map of tuple indices induces a map of the corresponding representable sums.
Source: Stacks 03AT (blueprint: lem-weil-pbc-site-cech-free-complex-exact). -/
def tupleMap {p q : ℕ} (α : Fin (q + 1) → Fin (p + 1)) :
    S.tuplePresheaf p ⟶ S.tuplePresheaf q where
  app X := ↾fun x ↦ ⟨x.1 ∘ α, x.2 ≫ S.indexMap x.1 α⟩
  naturality X Y g := by
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨x.1 ∘ α, (g.unop ≫ x.2) ≫ S.indexMap x.1 α⟩ :
      Σ t : Fin (q + 1) → T, Y.unop ⟶ S.W q t) =
      ⟨x.1 ∘ α, g.unop ≫ (x.2 ≫ S.indexMap x.1 α)⟩
    rw [Category.assoc]

/-- The simplicial representable sums; index-map laws follow from product uniqueness.
Source: Stacks 03AT (blueprint: lem-weil-pbc-site-cech-free-complex-exact). -/
abbrev tupleSimplicial : SimplicialObject (Cᵒᵖ ⥤ Type v) where
  obj n := S.tuplePresheaf n.unop.len
  map α := S.tupleMap α.unop.toOrderHom
  map_id n := by
    have hi (t : Fin (n.unop.len + 1) → T) : S.indexMap t id = 𝟙 _ := by
      obtain ⟨c, _, hu⟩ := S.universal n.unop.len t (S.W n.unop.len t)
        (S.pr n.unop.len t) (S.comm n.unop.len t)
      apply (hu _ ?_).trans (hu _ (fun k ↦ Category.id_comp _)).symm
      intro k
      exact S.indexMap_pr t id k
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨x.1 ∘ id, x.2 ≫ S.indexMap x.1 id⟩ :
      Σ t : Fin (n.unop.len + 1) → T, X.unop ⟶ S.W n.unop.len t) = x
    rw [hi, Category.comp_id]
    cases x
    rfl
  map_comp α β := by
    have hi (t) : S.indexMap t (α.unop.toOrderHom ∘ β.unop.toOrderHom) =
        S.indexMap t α.unop.toOrderHom ≫
          S.indexMap (t ∘ α.unop.toOrderHom) β.unop.toOrderHom := by
      let b := S.indexMap t α.unop.toOrderHom ≫
        S.indexMap (t ∘ α.unop.toOrderHom) β.unop.toOrderHom
      obtain ⟨c, _, hu⟩ := S.universal _ _ _
        (fun k ↦ b ≫ S.pr _ _ k)
        (fun k ↦ by simp only [Category.assoc, S.comm])
      apply (hu _ ?_).trans (hu b (fun _ ↦ rfl)).symm
      intro k
      dsimp [b]
      symm
      rw [Category.assoc]
      exact (congrArg (fun h ↦ S.indexMap t α.unop.toOrderHom ≫ h)
        (S.indexMap_pr (t ∘ α.unop.toOrderHom) β.unop.toOrderHom k)).trans
        ((S.indexMap_pr t α.unop.toOrderHom (β.unop.toOrderHom k)).trans
          (S.indexMap_pr t (α.unop.toOrderHom ∘ β.unop.toOrderHom) k).symm)
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨x.1 ∘ (α.unop.toOrderHom ∘ β.unop.toOrderHom),
      x.2 ≫ S.indexMap x.1 (α.unop.toOrderHom ∘ β.unop.toOrderHom)⟩ :
      Σ t : Fin (_ + 1) → T, X.unop ⟶ S.W _ t) =
      ⟨(x.1 ∘ α.unop.toOrderHom) ∘ β.unop.toOrderHom,
        (x.2 ≫ S.indexMap x.1 α.unop.toOrderHom) ≫
          S.indexMap (x.1 ∘ α.unop.toOrderHom) β.unop.toOrderHom⟩
    rw [hi, Category.assoc]
    rfl

/-- The actual alternating chain complex of free module presheaves on the tuple sums.
Source: Stacks 03F5 (blueprint: lem-weil-pbc-site-cech-free-complex-exact). -/
noncomputable abbrev freeComplex (R : Cᵒᵖ ⥤ RingCat.{v}) :
    ChainComplex (PresheafOfModules.{v} R) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj
    (S.tupleSimplicial ⋙ PresheafOfModules.free R)

private abbrev TupleBasis (p : ℕ) (X : Cᵒᵖ) :=
  Σ t : Fin (p + 1) → T, X.unop ⟶ S.W p t

private def tupleBase {p : ℕ} {X : Cᵒᵖ} (x : S.TupleBasis p X) : X.unop ⟶ U :=
  x.2 ≫ S.pr p x.1 0 ≫ hom (x.1 0)

private theorem tupleBase_eq {p : ℕ} {X : Cᵒᵖ} (x : S.TupleBasis p X)
    (i : Fin (p + 1)) : x.2 ≫ S.pr p x.1 i ≫ hom (x.1 i) = S.tupleBase x := by
  simp only [tupleBase, S.comm]

private noncomputable def selectedLift (X : Cᵒᵖ) (φ : X.unop ⟶ U)
    (h : ∃ l : Σ i : T, X.unop ⟶ f i, l.2 ≫ hom l.1 = φ) :
    Σ i : T, X.unop ⟶ f i := Classical.choose h

private theorem selectedLift_spec (X : Cᵒᵖ) (φ : X.unop ⟶ U)
    (h : ∃ l : Σ i : T, X.unop ⟶ f i, l.2 ≫ hom l.1 = φ) :
    (selectedLift X φ h).2 ≫ hom (selectedLift X φ h).1 = φ :=
  Classical.choose_spec h

private theorem tuple_has_lift {p : ℕ} {X : Cᵒᵖ} (x : S.TupleBasis p X) :
    ∃ l : Σ i : T, X.unop ⟶ f i, l.2 ≫ hom l.1 = S.tupleBase x :=
  ⟨⟨x.1 0, x.2 ≫ S.pr p x.1 0⟩, by rw [Category.assoc]; rfl⟩

private noncomputable def tupleLift {p : ℕ} {X : Cᵒᵖ} (x : S.TupleBasis p X) :
    Σ i : T, X.unop ⟶ f i :=
  selectedLift X (S.tupleBase x) (S.tuple_has_lift x)

private noncomputable def prefixIndices {p : ℕ} {X : Cᵒᵖ}
    (x : S.TupleBasis p X) : Fin (p + 2) → T :=
  Fin.cons (S.tupleLift x).1 x.1

private noncomputable def prefixArrows {p : ℕ} {X : Cᵒᵖ}
    (x : S.TupleBasis p X) : ∀ i, X.unop ⟶ f (S.prefixIndices x i) :=
  Fin.cases (S.tupleLift x).2 (fun i ↦ x.2 ≫ S.pr p x.1 i)

private theorem prefixArrows_comm {p : ℕ} {X : Cᵒᵖ}
    (x : S.TupleBasis p X) (i : Fin (p + 2)) :
    S.prefixArrows x i ≫ hom (S.prefixIndices x i) =
      S.prefixArrows x 0 ≫ hom (S.prefixIndices x 0) := by
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · rfl
  · change (x.2 ≫ S.pr p x.1 i) ≫ hom (x.1 i) =
      (S.tupleLift x).2 ≫ hom (S.tupleLift x).1
    rw [show (S.tupleLift x).2 ≫ hom (S.tupleLift x).1 = S.tupleBase x from
      selectedLift_spec X _ _]
    rw [Category.assoc]
    exact S.tupleBase_eq x i

private noncomputable def tuplePrefix {p : ℕ} {X : Cᵒᵖ}
    (x : S.TupleBasis p X) : S.TupleBasis (p + 1) X :=
  ⟨S.prefixIndices x, (S.universal (p + 1) (S.prefixIndices x) X.unop
    (S.prefixArrows x) (S.prefixArrows_comm x)).choose⟩

private theorem tuplePrefix_pr {p : ℕ} {X : Cᵒᵖ}
    (x : S.TupleBasis p X) (i : Fin (p + 2)) :
    (S.tuplePrefix x).2 ≫ S.pr (p + 1) (S.tuplePrefix x).1 i =
      S.prefixArrows x i :=
  (S.universal (p + 1) (S.prefixIndices x) X.unop
    (S.prefixArrows x) (S.prefixArrows_comm x)).choose_spec.1 i

private def tupleFace {p : ℕ} {X : Cᵒᵖ} (i : Fin (p + 2))
    (x : S.TupleBasis (p + 1) X) : S.TupleBasis p X :=
  ⟨x.1 ∘ i.succAbove, x.2 ≫ S.indexMap x.1 i.succAbove⟩

private theorem tuple_hom_ext {p : ℕ} {X : Cᵒᵖ} {t : Fin (p + 1) → T}
    {a b : X.unop ⟶ S.W p t} (h : ∀ i, a ≫ S.pr p t i = b ≫ S.pr p t i) :
    a = b := by
  obtain ⟨c, _, hc⟩ := S.universal p t X.unop (fun i ↦ b ≫ S.pr p t i)
    (fun i ↦ by simp only [Category.assoc, S.comm])
  exact (hc a h).trans (hc b (fun _ ↦ rfl)).symm

private theorem tupleFace_pr {p : ℕ} {X : Cᵒᵖ} (i : Fin (p + 2))
    (x : S.TupleBasis (p + 1) X) (k : Fin (p + 1)) :
    (S.tupleFace i x).2 ≫ S.pr p (S.tupleFace i x).1 k =
      x.2 ≫ S.pr (p + 1) x.1 (i.succAbove k) := by
  dsimp [tupleFace]
  rw [Category.assoc, S.indexMap_pr]

private theorem tupleFace_base {p : ℕ} {X : Cᵒᵖ} (i : Fin (p + 2))
    (x : S.TupleBasis (p + 1) X) : S.tupleBase (S.tupleFace i x) = S.tupleBase x := by
  unfold tupleBase
  rw [← Category.assoc, S.tupleFace_pr, Category.assoc]
  exact S.tupleBase_eq x _

private theorem tuple_ext {p : ℕ} {X : Cᵒᵖ} {x y : S.TupleBasis p X}
    (ht : x.1 = y.1)
    (h : ∀ k, HEq (x.2 ≫ S.pr p x.1 k) (y.2 ≫ S.pr p y.1 k)) : x = y := by
  obtain ⟨t, a⟩ := x
  obtain ⟨t', b⟩ := y
  dsimp at ht
  subst t'
  have hab : a = b := S.tuple_hom_ext (fun k ↦ eq_of_heq (h k))
  cases hab
  rfl

private theorem tupleFace_prefix_zero {p : ℕ} {X : Cᵒᵖ} (x : S.TupleBasis p X) :
    S.tupleFace 0 (S.tuplePrefix x) = x := by
  apply S.tuple_ext
  · funext i
    simp [tupleFace, tuplePrefix, prefixIndices]
  · intro i
    rw [S.tupleFace_pr]
    simp only [Fin.zero_succAbove]
    rw [S.tuplePrefix_pr]
    rfl

private theorem tupleLift_face {p : ℕ} {X : Cᵒᵖ} (i : Fin (p + 2))
    (x : S.TupleBasis (p + 1) X) : S.tupleLift (S.tupleFace i x) = S.tupleLift x := by
  unfold tupleLift
  congr 1
  exact S.tupleFace_base i x

private theorem tupleFace_prefix_succ {p : ℕ} {X : Cᵒᵖ}
    (i : Fin (p + 2)) (x : S.TupleBasis (p + 1) X) :
    S.tupleFace i.succ (S.tuplePrefix x) = S.tuplePrefix (S.tupleFace i x) := by
  apply S.tuple_ext
  · change (Fin.cons (S.tupleLift x).1 x.1) ∘ i.succ.succAbove =
      Fin.cons (S.tupleLift (S.tupleFace i x)).1 (x.1 ∘ i.succAbove)
    rw [S.tupleLift_face]
    exact Fin.cons_comp_succ_succAbove _ _ _
  · intro k
    rw [S.tupleFace_pr, S.tuplePrefix_pr, S.tuplePrefix_pr]
    refine Fin.cases ?_ (fun k ↦ ?_) k
    · change HEq (S.prefixArrows x (i.succ.succAbove 0))
        (S.tupleLift (S.tupleFace i x)).2
      erw [Fin.succ_succAbove_zero]
      change HEq (S.tupleLift x).2 (S.tupleLift (S.tupleFace i x)).2
      exact (Sigma.ext_iff.mp (S.tupleLift_face i x).symm).2
    · change HEq (S.prefixArrows x (i.succ.succAbove k.succ))
        ((S.tupleFace i x).2 ≫ S.pr p (S.tupleFace i x).1 k)
      erw [Fin.succ_succAbove_succ]
      change HEq (x.2 ≫ S.pr (p + 1) x.1 (i.succAbove k))
        ((S.tupleFace i x).2 ≫ S.pr p (S.tupleFace i x).1 k)
      rw [S.tupleFace_pr]

private noncomputable def freePrefix (R : Cᵒᵖ ⥤ RingCat.{v}) (p : ℕ) (X : Cᵒᵖ) :
    ((S.freeComplex R).X p).obj X ⟶ ((S.freeComplex R).X (p + 1)).obj X :=
  (ModuleCat.free (R.obj X)).map (↾fun x ↦ S.tuplePrefix x)

private noncomputable def freeFace (R : Cᵒᵖ ⥤ RingCat.{v}) (p : ℕ) (X : Cᵒᵖ)
    (i : Fin (p + 2)) :
    ((S.freeComplex R).X (p + 1)).obj X ⟶ ((S.freeComplex R).X p).obj X :=
  (ModuleCat.free (R.obj X)).map (↾fun x ↦ S.tupleFace i x)

private theorem freePrefix_face_zero (R : Cᵒᵖ ⥤ RingCat.{v}) (p : ℕ) (X : Cᵒᵖ) :
    S.freePrefix R p X ≫ S.freeFace R p X 0 = 𝟙 _ := by
  change (ModuleCat.free (R.obj X)).map (↾fun x ↦ S.tuplePrefix x) ≫
    (ModuleCat.free (R.obj X)).map (↾fun x ↦ S.tupleFace 0 x) = 𝟙 _
  rw [← Functor.map_comp, ← Functor.map_id]
  congr 1
  apply ConcreteCategory.hom_ext
  intro x
  exact S.tupleFace_prefix_zero x

private theorem freePrefix_face_succ (R : Cᵒᵖ ⥤ RingCat.{v}) (p : ℕ) (X : Cᵒᵖ)
    (i : Fin (p + 2)) :
    S.freePrefix R (p + 1) X ≫ S.freeFace R (p + 1) X i.succ =
      S.freeFace R p X i ≫ S.freePrefix R p X := by
  change (ModuleCat.free (R.obj X)).map (↾fun x ↦ S.tuplePrefix x) ≫
      (ModuleCat.free (R.obj X)).map (↾fun x ↦ S.tupleFace i.succ x) =
    (ModuleCat.free (R.obj X)).map (↾fun x ↦ S.tupleFace i x) ≫
      (ModuleCat.free (R.obj X)).map (↾fun x ↦ S.tuplePrefix x)
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply ConcreteCategory.hom_ext
  intro x
  exact S.tupleFace_prefix_succ i x

open scoped BigOperators in
private theorem freeComplex_d_app (R : Cᵒᵖ ⥤ RingCat.{v}) (p : ℕ) (X : Cᵒᵖ) :
    ((S.freeComplex R).d (p + 1) p).app X =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • S.freeFace R p X i := by
  simp only [freeComplex, AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD]
  change (PresheafOfModules.evaluation R X).map
    (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
      SimplicialObject.δ (S.tupleSimplicial ⋙ PresheafOfModules.free R) i) = _
  rw [Functor.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Functor.map_zsmul]
  congr 1

/-- The evaluated free Čech complex has a contracting identity in each positive degree.
Source: Stacks Project, Cohomology on Sites, Tags 03AT and 03F5.
(blueprint: lem-weil-pbc-site-cech-free-complex-exact-fibrewise)

Proof: Fix X. For each basis tuple x, its projections have a common composite
φ:X→U. The zeroth projection proves that φ has a lift to one of the f(i).
Choose a lift depending only on φ; proof irrelevance makes this independent
of the existence proof. Prefix it to the projections of x, using the unique
product lift to construct the resulting basis tuple. Deleting coordinate zero
returns x. Deleting coordinate i+1 commutes with prefixing after deleting i,
since deletion preserves φ and hence preserves the selected lift.
Apply ModuleCat.free to extend these functions R(X)-linearly. Evaluation is
additive, so the differential is the alternating sum of the free face maps.
In h followed by d, the zeroth face gives the identity and each successor face
cancels its opposite-signed term in d followed by k. This works also for n=0.
If T is empty there are no basis tuples and no nonexistent lift is chosen.
These maps are constructed only at the fixed X; no naturality is asserted. -/
theorem freeComplex_evaluation_contracting (R : Cᵒᵖ ⥤ RingCat.{v})
    (n : ℕ) (X : Cᵒᵖ) :
    ∃ h : ((S.freeComplex R).X (n + 1)).obj X ⟶
        ((S.freeComplex R).X (n + 2)).obj X,
      ∃ k : ((S.freeComplex R).X n).obj X ⟶
          ((S.freeComplex R).X (n + 1)).obj X,
        h ≫ ((S.freeComplex R).d (n + 2) (n + 1)).app X +
          ((S.freeComplex R).d (n + 1) n).app X ≫ k = 𝟙 _ := by
  refine ⟨S.freePrefix R (n + 1) X, S.freePrefix R n X, ?_⟩
  rw [S.freeComplex_d_app R (n + 1) X, S.freeComplex_d_app R n X]
  rw [Preadditive.comp_sum, Fin.sum_univ_succ]
  simp only [Preadditive.comp_zsmul, Fin.val_zero, pow_zero, one_smul,
    S.freePrefix_face_zero, Fin.val_succ, pow_succ, mul_neg_one,
    neg_smul, Preadditive.comp_neg, S.freePrefix_face_succ,
    Preadditive.sum_comp, Preadditive.zsmul_comp]
  rw [Finset.sum_neg_distrib]
  simp

end CategoryTheory.SiteCechComplex
