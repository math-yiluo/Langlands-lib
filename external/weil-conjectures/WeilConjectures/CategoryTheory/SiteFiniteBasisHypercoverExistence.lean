/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.Precoverage
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import WeilConjectures.CategoryTheory.ProperFaceMatchingObject
import WeilConjectures.CategoryTheory.SiteFiniteBasisHypercoverStep

/-!
# Hypercovers finite in each degree from a finite covering basis

Source: Stacks Project, Hypercoverings, Tag 094K (lemma-w-contractible), using the
split-skeleton construction of Tag 0DAV and the hypercover definition of Tag 01G5.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory

private theorem tower_restrict {D : Type u} [Category D]
    (K : ∀ n, SimplicialObject.Truncated D n)
    (e : ∀ n, (SimplicialObject.Truncated.trunc D (n + 1) n).obj (K (n + 1)) = K n)
    (n m : ℕ) (h : m ≤ n) :
    (SimplicialObject.Truncated.trunc D n m h).obj (K n) = K m := by
  induction n generalizing m with
  | zero =>
    obtain rfl : m = 0 := Nat.eq_zero_of_le_zero h
    rfl
  | succ n ih =>
    obtain rfl | h := eq_or_lt_of_le h
    · rfl
    · have hn := ih m (Nat.le_of_lt_succ h)
      have he := congrArg
        (fun L ↦ (SimplicialObject.Truncated.trunc D n m (Nat.le_of_lt_succ h)).obj L)
        (e n)
      exact he.trans hn

private def towerObj {D : Type u} [Category D]
    (K : ∀ n, SimplicialObject.Truncated D n)
    (X : SimplexCategoryᵒᵖ) : D :=
  (K X.unop.len).obj (op ⟨X.unop, le_rfl⟩)

private theorem towerObj_eq {D : Type u} [Category D]
    (K : ∀ n, SimplicialObject.Truncated D n)
    (e : ∀ n, (SimplicialObject.Truncated.trunc D (n + 1) n).obj (K (n + 1)) = K n)
    (X : SimplexCategoryᵒᵖ) (n : ℕ) (h : X.unop.len ≤ n) :
    towerObj K X = (K n).obj (op ⟨X.unop, h⟩) :=
  (Functor.congr_obj (tower_restrict K e n X.unop.len h) (op ⟨X.unop, le_rfl⟩)).symm

private def towerMapAt {D : Type u} [Category D]
    (K : ∀ n, SimplicialObject.Truncated D n)
    (e : ∀ n, (SimplicialObject.Truncated.trunc D (n + 1) n).obj (K (n + 1)) = K n)
    {X Y : SimplexCategoryᵒᵖ} (f : X ⟶ Y)
    (n : ℕ) (hX : X.unop.len ≤ n) (hY : Y.unop.len ≤ n) :
    towerObj K X ⟶ towerObj K Y :=
  eqToHom (towerObj_eq K e X n hX) ≫
    (K n).map (SimplexCategory.Truncated.Hom.tr f.unop hY hX).op ≫
      eqToHom (towerObj_eq K e Y n hY).symm

private theorem towerMapAt_eq {D : Type u} [Category D]
    (K : ∀ n, SimplicialObject.Truncated D n)
    (e : ∀ n, (SimplicialObject.Truncated.trunc D (n + 1) n).obj (K (n + 1)) = K n)
    {X Y : SimplexCategoryᵒᵖ} (f : X ⟶ Y)
    (n m : ℕ) (hX : X.unop.len ≤ n) (hY : Y.unop.len ≤ n)
    (hXm : X.unop.len ≤ m) (hYm : Y.unop.len ≤ m) :
    towerMapAt K e f n hX hY = towerMapAt K e f m hXm hYm := by
  suffices lower : ∀ (a b : ℕ) (ha : X.unop.len ≤ a) (ha' : Y.unop.len ≤ a)
      (hb : X.unop.len ≤ b) (hb' : Y.unop.len ≤ b), a ≤ b →
      towerMapAt K e f b hb hb' = towerMapAt K e f a ha ha' by
    rcases le_total n m with h | h
    · exact (lower n m hX hY hXm hYm h).symm
    · exact lower m n hXm hYm hX hY h
  intro a b ha ha' hb hb' hab
  have hm := Functor.congr_hom (tower_restrict K e b a hab)
    (SimplexCategory.Truncated.Hom.tr f.unop ha' ha).op
  dsimp [SimplicialObject.Truncated.trunc] at hm
  unfold towerMapAt
  rw [hm]
  simp only [← Category.assoc, eqToHom_trans]
  simp only [Category.assoc, eqToHom_trans]

private def towerGlue {D : Type u} [Category D]
    (K : ∀ n, SimplicialObject.Truncated D n)
    (e : ∀ n, (SimplicialObject.Truncated.trunc D (n + 1) n).obj (K (n + 1)) = K n) :
    SimplicialObject D where
  obj := towerObj K
  map {X Y} f := towerMapAt K e f (max X.unop.len Y.unop.len)
    (le_max_left _ _) (le_max_right _ _)
  map_id X := by
    simp [towerMapAt]
  map_comp {X Y Z} f g := by
    let n := max X.unop.len (max Y.unop.len Z.unop.len)
    have hX : X.unop.len ≤ n := le_max_left _ _
    have hY : Y.unop.len ≤ n := (le_max_left _ _).trans (le_max_right _ _)
    have hZ : Z.unop.len ≤ n := (le_max_right _ _).trans (le_max_right _ _)
    rw [towerMapAt_eq K e (f ≫ g) _ n _ _ hX hZ,
      towerMapAt_eq K e f _ n _ _ hX hY, towerMapAt_eq K e g _ n _ _ hY hZ]
    simp only [towerMapAt, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    rw [show (SimplexCategory.Truncated.Hom.tr (f ≫ g).unop hZ hX).op =
      (SimplexCategory.Truncated.Hom.tr f.unop hY hX).op ≫
        (SimplexCategory.Truncated.Hom.tr g.unop hZ hY).op from rfl, Functor.map_comp]
    simp only [Category.assoc]

private theorem towerGlue_restrict {D : Type u} [Category D]
    (K : ∀ n, SimplicialObject.Truncated D n)
    (e : ∀ n, (SimplicialObject.Truncated.trunc D (n + 1) n).obj (K (n + 1)) = K n)
    (n : ℕ) : (SimplicialObject.truncation n).obj (towerGlue K e) = K n := by
  refine Functor.ext
    (fun X ↦ towerObj_eq K e (op X.unop.obj) n X.unop.property) ?_
  intro X Y f
  exact towerMapAt_eq K e
    ((SimplexCategory.Truncated.inclusion n).op.map f) _ n _ _
    X.unop.property Y.unop.property


open FormalSplitAttachment in
private theorem zero_split {D : Type u} [Category D] (F : FormalCoproduct.{max u v} D) :
    IsSplit ((Functor.const _).obj F : SimplicialObject.Truncated _ 0) := by
  let K : SimplicialObject.Truncated (FormalCoproduct.{max u v} D) 0 := (Functor.const _).obj F
  have hn (q : Fin 1) (i : (term K q).I) : IsNondegenerate K q i := by
    rintro ⟨r, hr, σ, hσ, j, hj⟩
    have hq : q.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ q.isLt)
    omega
  refine ⟨?_, ?_⟩
  · intro q
    have hq : q = 0 := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ q.isLt))
    subst q
    constructor
    · rintro ⟨r, σ, i⟩ ⟨s, τ, j⟩ h
      have hr : r = 0 := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ r.isLt))
      have hs : s = 0 := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ s.isLt))
      subst r s
      have hστ : σ = τ := Subtype.ext (by
        apply SimplexCategory.Hom.ext
        apply OrderHom.ext
        funext x
        apply Fin.ext
        have hσ := (σ.val.toOrderHom x).isLt
        have hτ := (τ.val.toOrderHom x).isLt
        change _ < 1 at hσ hτ
        omega)
      subst τ
      have hij : i = j := Subtype.ext h
      subst j
      rfl
    · intro i
      exact ⟨⟨0, ⟨𝟙 _, inferInstance⟩, ⟨i, hn 0 i⟩⟩, rfl⟩
  · intro q a
    change IsIso (𝟙 _)
    infer_instance

open FormalSplitAttachment in
private theorem exists_zero_truncation
    {C : Type u} [Category.{v} C] (J : Precoverage C) (B : Set C) (T : C)
    (I : Type (max u v)) (U : I → C) (f : ∀ i, U i ⟶ T)
    (hI : Finite I) (hB : ∀ i, U i ∈ B) (hf : Presieve.ofArrows U f ∈ J T) :
    ∃ K : SimplicialObject.Truncated (FormalCoproduct.{max u v} (Over T)) 0,
      IsFiniteBasisTruncation J B T K := by
  let F : FormalCoproduct.{max u v} (Over T) := ⟨I, fun i ↦ Over.mk (f i)⟩
  let K : SimplicialObject.Truncated (FormalCoproduct.{max u v} (Over T)) 0 :=
    (Functor.const _).obj F
  refine ⟨K, zero_split F, ?_⟩
  intro q
  have hq : q = 0 := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ q.isLt))
  subst q
  refine ⟨hI, hB, ?_⟩
  let Z := (FormalCoproduct.incl (Over T)).obj (Over.mk (𝟙 T))
  have empty (a : SimplicialObject.ProperFaceCategory 0) : False :=
    Nat.not_lt_zero _ a.property.1
  let M : Cone (faceDiagram K 0) :=
    ⟨Z, { app := fun a ↦ (empty a.unop).elim
          naturality := fun X Y f ↦ (empty X.unop).elim }⟩
  let μ : F ⟶ Z := ⟨fun _ ↦ PUnit.unit,
    fun i ↦ Over.homMk (f i) (by simp [Z, F, FormalCoproduct.incl])⟩
  have ht : IsTerminal Z := FormalCoproduct.isTerminalIncl _ Over.mkIdTerminal
  refine ⟨M, μ, fun _ ↦ rfl, ⟨?_⟩, ?_, ?_⟩
  · exact { lift := fun s ↦ ht.from s.pt
            fac := fun s a ↦ (empty a.unop).elim
            uniq := fun s m hm ↦ ht.hom_ext _ _ }
  · intro a
    exact (empty a).elim
  · intro j
    change PUnit at j
    cases j
    have he : Presieve.ofArrows
        (fun i : {i : I // μ.f i = PUnit.unit} ↦ U i.val)
        (fun i : {i : I // μ.f i = PUnit.unit} ↦ f i.val) =
        Presieve.ofArrows U f :=
      Presieve.ofArrows_comp_eq_of_surjective f (fun i ↦ ⟨⟨i, rfl⟩, rfl⟩)
    simpa [μ, Z, F, FormalCoproduct.incl, Over.homMk] using he.symm ▸ hf

/-- A finite covering basis gives a hypercover finite in every degree.
Source: Stacks Project, Hypercoverings, Tags 094K, 0DAV and 01G5.
(auxiliary; not a blueprint node)

Proof: Work in the slice over `T`, whose terminal object is `id_T`, whose pullbacks
are those of `C`, and whose covers are the underlying covers. Choose a finite basis
cover in degree zero. Terminal objects and pullbacks give finite limits
[lem-weil-pbc-finite-limits-from-terminal-pullbacks]. The terminal formal family is
`{id_T}` and pullbacks of formal families have components the componentwise pullbacks,
indexed by pairs with equal target index [def-weil-pbc-formal-coproduct]. Finite-index
families are closed under these operations, so finite boundary limits have finite
index sets, with the same universal property against arbitrary formal families.
Inductively cover each component of the next boundary limit by a finite basis cover.
Attach those as the new nondegenerate simplices to the split truncation, retaining
the prescribed degenerate copies [lem-weil-pbc-site-hypercover-finite-extension].
Its terms remain finite basis families: only finitely many surjections between finite
ordered sets occur. The attachment theorem gives all operators and composition laws.
For each matching component, repeatedly adjoin the finitely many prescribed degenerate
arrows to the chosen cover; the adjoining hypothesis shows the resulting family covers.
This includes empty covers and empty matching families. Recursively choose extensions.
Each degree and each operator stabilizes; taking their permanent values gives a functor,
since each functor identity can be checked at a finite stage containing its degrees
[def-weil-pbc-simplicial-object]. The slice gives the augmentation and degree-zero
matching object. Every fixed degree retains its finite basis family and matching cover. -/
theorem exists_site_finite_basis_hypercover
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    (J : Precoverage C)
    (B : Set C)
    (hcover : ∀ T : C, ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i : I, U i ⟶ T),
      Finite I ∧ (∀ i : I, U i ∈ B) ∧ Presieve.ofArrows U f ∈ J T)
    (hadjoin : ∀ (T : C) (I : Type (max u v)) [Finite I] (U : I → C)
      (f : ∀ i : I, U i ⟶ T), (∀ i : I, U i ∈ B) →
      Presieve.ofArrows U f ∈ J T → ∀ (V : C), V ∈ B → ∀ (g : V ⟶ T),
        Presieve.ofArrows U f ⊔ Presieve.singleton g ∈ J T)
    (T : C) :
    ∃ (K : SimplicialObject (FormalCoproduct.{max u v} (Over T)))
      (M : ∀ n : ℕ, Cone (K.properFaceDiagram n))
      (μ : ∀ n : ℕ, K _⦋n⦌ ⟶ (M n).pt),
      (∀ n : ℕ, Finite (K _⦋n⦌).I) ∧
      (∀ (n : ℕ) (i : (K _⦋n⦌).I), ((K _⦋n⦌).obj i).left ∈ B) ∧
      (M 0).pt = (FormalCoproduct.incl (Over T)).obj (Over.mk (𝟙 T)) ∧
      (∀ n : ℕ, Nonempty (IsLimit (M n))) ∧
      (∀ (n : ℕ) (a : SimplicialObject.ProperFaceCategory n),
        μ n ≫ (M n).π.app (op a) = K.map a.obj.hom.op) ∧
      (∀ (n : ℕ) (j : (M n).pt.I),
        Presieve.ofArrows
          (fun i : {i : (K _⦋n⦌).I // (μ n).f i = j} ↦ ((K _⦋n⦌).obj i.val).left)
          (fun i : {i : (K _⦋n⦌).I // (μ n).f i = j} ↦
            ((μ n).φ i.val).left ≫
              eqToHom (congrArg (fun k ↦ ((M n).pt.obj k).left) i.property)) ∈
          J ((M n).pt.obj j).left) := by
  classical
  obtain ⟨I, U, f, hI, hB, hf⟩ := hcover T
  obtain ⟨K₀, hK₀⟩ := exists_zero_truncation J B T I U f hI hB hf
  let A (n : ℕ) := {K : SimplicialObject.Truncated (FormalCoproduct.{max u v} (Over T)) n //
    FormalSplitAttachment.IsFiniteBasisTruncation J B T K}
  have hstep (n : ℕ) (a : A n) :=
    FormalSplitAttachment.exists_finite_basis_truncation_extension
      J B hcover hadjoin T n a.val a.property
  choose next he hnext using hstep
  let s : ∀ n, A n := Nat.rec ⟨K₀, hK₀⟩ (fun n a ↦ ⟨next n a, hnext n a⟩)
  let k (n : ℕ) := (s n).val
  have e (n : ℕ) : (SimplicialObject.Truncated.trunc _ (n + 1) n).obj (k (n + 1)) =
      k n := he n (s n)
  let K := towerGlue k e
  have hg (n : ℕ) :
      FormalSplitAttachment.IsFiniteBasisTruncation J B T
        ((SimplicialObject.truncation n).obj K) := by
    rw [towerGlue_restrict]
    exact (s n).property
  have hd (n : ℕ) := (hg n).2 ⟨n, Nat.lt_succ_self n⟩
  choose M μ hzero hlim hproj hcov using fun n ↦ (hd n).2.2
  exact ⟨K, M, μ, fun n ↦ (hd n).1, fun n ↦ (hd n).2.1,
    hzero 0 rfl, hlim, hproj, hcov⟩

end CategoryTheory
