/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CompactObject
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Compact Hom commutes with sequential homotopy colimits

Source: Stacks Project, Derived Categories, Lemma 13.33.9 (Tag 094A)
(blueprint: lem-pc-compact-hom-hocolim).
-/

@[expose] public section

universe w v u

open CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace CategoryTheory

open Classical in
private theorem compact_projection_zero
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (K : C) (hK : IsCompactObject K)
    {I : Type w} (E : I → C) (f : K ⟶ ∐ E)
    (hf : ∀ i, f ≫ Sigma.π E i = 0) : f = 0 := by
  classical
  let c := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp K (Sigma.ι E i))
  have hc : ∀ (x : DirectSum I (fun i ↦ (K ⟶ E i))) (j : I), c x ≫ Sigma.π E j = x j := by
    intro x j
    induction x using DirectSum.induction_on with
    | zero => simp [c]
    | of i x =>
      by_cases h : i = j
      · subst j
        simp [c, Preadditive.rightComp, Category.assoc]
      · simp [c, Preadditive.rightComp, Category.assoc, Sigma.ι_π_of_ne _ h,
          DirectSum.of_apply, h]
    | add x y hx hy => simp [map_add, Preadditive.add_comp, hx, hy]
  obtain ⟨x, rfl⟩ := (hK I E).2 f
  change c x = 0
  have hx : x = 0 := by
    ext i
    exact (hc x i).symm.trans (hf i)
  rw [hx, map_zero]

private theorem telescope_hom_zero
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (K : C) (hK : IsCompactObject K) (X : ℕ ⥤ C)
    (f : K ⟶ ∐ fun n : ULift.{w} ℕ ↦ X.obj n.down)
    (hf : f ≫ (𝟙 _ - Sigma.desc (fun n : ULift.{w} ℕ ↦
      X.map (homOfLE (Nat.le_succ n.down)) ≫
        Sigma.ι (fun k : ULift.{w} ℕ ↦ X.obj k.down) ⟨n.down + 1⟩)) = 0) :
    f = 0 := by
  classical
  let : DecidableEq (ULift.{w} ℕ) := Classical.decEq _
  let A := fun n : ULift.{w} ℕ ↦ X.obj n.down
  let s : (∐ A) ⟶ ∐ A := Sigma.desc (fun n : ULift.{w} ℕ ↦
    X.map (homOfLE (Nat.le_succ n.down)) ≫ Sigma.ι A ⟨n.down + 1⟩)
  have hs0 : s ≫ Sigma.π A ⟨0⟩ = 0 := by
    apply Sigma.hom_ext
    intro j
    have hne : (⟨j.down + 1⟩ : ULift.{w} ℕ) ≠ ⟨0⟩ := by
      intro h
      have hh := congrArg ULift.down h
      dsimp at hh
      omega
    simp [s, Sigma.ι_π_of_ne _ hne]
  have hs : ∀ n : ℕ, s ≫ Sigma.π A ⟨n + 1⟩ =
      Sigma.π A ⟨n⟩ ≫ X.map (homOfLE (Nat.le_succ n)) := by
    intro n
    apply Sigma.hom_ext
    intro j
    by_cases h : j = ⟨n⟩
    · subst j
      simp [s, A]
    · have h' : (⟨j.down + 1⟩ : ULift.{w} ℕ) ≠ ⟨n + 1⟩ := by
        intro he
        apply h
        apply ULift.ext
        have hh := congrArg ULift.down he
        dsimp at hh ⊢
        omega
      simp [s, Sigma.ι_π_of_ne_assoc _ h, Sigma.ι_π_of_ne _ h']
  have he : f = f ≫ s := by
    simpa only [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] using hf
  apply compact_projection_zero K hK A f
  intro j
  obtain ⟨n⟩ := j
  induction n with
  | zero =>
    calc f ≫ Sigma.π A ⟨0⟩ = f ≫ s ≫ Sigma.π A ⟨0⟩ := by rw [← Category.assoc, ← he]
         _ = 0 := by rw [hs0, comp_zero]
  | succ n ih =>
    calc f ≫ Sigma.π A ⟨n + 1⟩ = f ≫ s ≫ Sigma.π A ⟨n + 1⟩ := by
           rw [← Category.assoc, ← he]
         _ = 0 := by rw [hs n, ← Category.assoc, ih, zero_comp]

private theorem telescope_map_hom_zero
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (K : C) (hK : IsCompactObject K)
    (X : ℕ ⥤ C) (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
    (f : K ⟶ F.obj (∐ fun n : ULift.{w} ℕ ↦ X.obj n.down))
    (hf : f ≫ F.map (𝟙 _ - Sigma.desc (fun n : ULift.{w} ℕ ↦
      X.map (homOfLE (Nat.le_succ n.down)) ≫
        Sigma.ι (fun k : ULift.{w} ℕ ↦ X.obj k.down) ⟨n.down + 1⟩)) = 0) :
    f = 0 := by
  let A := fun n : ULift.{w} ℕ ↦ X.obj n.down
  let d : (∐ A) ⟶ ∐ A := 𝟙 _ - Sigma.desc (fun n : ULift.{w} ℕ ↦
    X.map (homOfLE (Nat.le_succ n.down)) ≫ Sigma.ι A ⟨n.down + 1⟩)
  let B := fun n : ULift.{w} ℕ ↦ F.obj (X.obj n.down)
  let e : (∐ B) ⟶ ∐ B := 𝟙 _ - Sigma.desc (fun n : ULift.{w} ℕ ↦
    F.map (X.map (homOfLE (Nat.le_succ n.down))) ≫ Sigma.ι B ⟨n.down + 1⟩)
  let s := sigmaComparison F A
  have hs : e ≫ s = s ≫ F.map d := by
    apply Sigma.hom_ext
    intro j
    simp [e, d, s, B, A, Preadditive.comp_sub, Preadditive.sub_comp,
      Functor.map_sub, Category.assoc]
  have hi : inv s ≫ e = F.map d ≫ inv s := by
    apply (cancel_mono s).1
    simp only [Category.assoc, hs, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id,
      Category.comp_id]
  have hz : f ≫ inv s = 0 := telescope_hom_zero K hK (X ⋙ F) (f ≫ inv s) (by
    change (f ≫ inv s) ≫ e = 0
    rw [Category.assoc, hi, ← Category.assoc, hf, zero_comp])
  calc f = (f ≫ inv s) ≫ s := by simp
       _ = 0 := by rw [hz, zero_comp]

private theorem telescope_boundary_eventually_zero
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (K : C) (hK : IsCompactObject K)
    (X : ℕ ⥤ C) (n : ℕ) (f : K ⟶ X.obj n)
    (g : K ⟶ ∐ fun n : ULift.{w} ℕ ↦ X.obj n.down)
    (hf : f ≫ Sigma.ι (fun k : ULift.{w} ℕ ↦ X.obj k.down) ⟨n⟩ =
      g ≫ (𝟙 _ - Sigma.desc (fun j : ULift.{w} ℕ ↦
        X.map (homOfLE (Nat.le_succ j.down)) ≫
          Sigma.ι (fun k : ULift.{w} ℕ ↦ X.obj k.down) ⟨j.down + 1⟩))) :
    ∃ (m : ℕ) (hn : n ≤ m), f ≫ X.map (homOfLE hn) = 0 := by
  classical
  let : DecidableEq (ULift.{w} ℕ) := Classical.decEq _
  let A := fun j : ULift.{w} ℕ ↦ X.obj j.down
  let d : (∐ A) ⟶ ∐ A := 𝟙 _ - Sigma.desc (fun j : ULift.{w} ℕ ↦
    X.map (homOfLE (Nat.le_succ j.down)) ≫ Sigma.ι A ⟨j.down + 1⟩)
  let p (m : ℕ) : (∐ A) ⟶ X.obj m := Sigma.desc (fun j : ULift.{w} ℕ ↦
    if h : j.down ≤ m then X.map (homOfLE h) else 0)
  have hp : ∀ (j : ULift.{w} ℕ) (m : ℕ), j.down < m →
      Sigma.ι A j ≫ d ≫ p m = 0 := by
    intro j m hj
    have hj' : j.down + 1 ≤ m := hj
    simp [d, p, A, Category.assoc, Preadditive.comp_sub, Preadditive.sub_comp,
      hj.le, hj',
      ← X.map_comp]
  let c := DirectSum.toAddMonoid (fun j ↦ Preadditive.rightComp K (Sigma.ι A j))
  have hb : ∀ x : DirectSum (ULift.{w} ℕ) (fun j ↦ (K ⟶ A j)),
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → c x ≫ d ≫ p m = 0 := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact ⟨0, by intro m hm; simp⟩
    | of j a =>
      refine ⟨j.down + 1, ?_⟩
      intro m hm
      simpa [c, Preadditive.rightComp, Category.assoc] using
        congrArg (fun t ↦ a ≫ t) (hp j m hm)
    | add x y hx hy =>
      obtain ⟨N, hN⟩ := hx
      obtain ⟨M, hM⟩ := hy
      refine ⟨max N M, ?_⟩
      intro m hm
      simp [map_add, Preadditive.add_comp, hN m (le_trans (le_max_left _ _) hm),
        hM m (le_trans (le_max_right _ _) hm)]
  obtain ⟨x, hx⟩ := (hK (ULift.{w} ℕ) A).2 g
  obtain ⟨N, hN⟩ := hb x
  let m := max N n
  have hn : n ≤ m := le_max_right _ _
  refine ⟨m, hn, ?_⟩
  have hz : g ≫ d ≫ p m = 0 := by
    rw [← hx]
    exact hN m (le_max_left _ _)
  have he := congrArg (fun t ↦ t ≫ p m) hf
  change (f ≫ Sigma.ι A ⟨n⟩) ≫ p m = (g ≫ d) ≫ p m at he
  rw [Category.assoc g d (p m), hz] at he
  simpa [p, A, Category.assoc, hn] using he


/-- For compact `K`, the canonical comparison from the sequential colimit of `Hom(K, X n)`
to `Hom(K, Y)` is bijective when `Y` belongs to the telescope triangle.
Source: Stacks Project, Derived Categories, Tag 094A
(blueprint: lem-pc-compact-hom-hocolim).

The equations on the stage maps specify the canonical comparison uniquely by the colimit
universal property. The coproduct index is lifted to the universe of compactness.

Proof: put `A = ⨁ X n`. Compactness (`def-pc-compact-object`) identifies `Hom(K, A)`
and `Hom(K, A[1])` with the sums of `Hom(K, X n)` and `Hom(K, X n[1])`.
The endomorphism induced by identity minus shift becomes identity minus the transition
shift on these sums. It is injective: its zeroth component forces the zeroth input to vanish,
and induction forces every later component to vanish. Apply triangle exactness
(`lem-weil-pbc-hom-into-triangle-exact`) and the vanishing of consecutive compositions to
the telescope triangle and its rotation. Every map `K → Y` then factors through `q`, and
the kernel of postcomposition with `q` is the image of identity minus shift.
Construct the comparison by the colimit universal property using stage compatibility.
Direct-sum induction combines every finite sum of stage maps at one common later stage,
so the comparison is surjective. For injectivity, triangle exactness expresses the difference
of two representatives at a common stage as a telescope boundary. Compactness writes its
preimage as a finite sum. The truncated map from the coproduct to stage `m`, sending each
stage `j ≤ m` along its transition and the other stages to zero, kills every boundary
summand with `j < m`. Taking `m` beyond the finite support shows that the difference
vanishes at a later stage. The colimit relations identify the two representatives. -/
theorem compact_hom_hocolim
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C] [HasCoproducts.{w} C]
    (K : C) (hK : IsCompactObject K) (X : ℕ ⥤ C) (Y : C)
    (q : (∐ fun n : ULift.{w} ℕ ↦ X.obj n.down) ⟶ Y)
    (r : Y ⟶ (∐ fun n : ULift.{w} ℕ ↦ X.obj n.down)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk
      (𝟙 (∐ fun n : ULift.{w} ℕ ↦ X.obj n.down) -
        Sigma.desc (fun n : ULift.{w} ℕ ↦
          X.map (homOfLE (Nat.le_succ n.down)) ≫
            Sigma.ι (fun k : ULift.{w} ℕ ↦ X.obj k.down) ⟨n.down + 1⟩))
      q r ∈ distTriang C) :
    ∃ φ : colimit (X ⋙ coyoneda.obj (op K)) → (K ⟶ Y),
      (∀ (n : ℕ) (f : K ⟶ X.obj n),
        φ (colimit.ι (X ⋙ coyoneda.obj (op K)) n f) =
          f ≫ Sigma.ι (fun k : ULift.{w} ℕ ↦ X.obj k.down) ⟨n⟩ ≫ q) ∧
      Function.Bijective φ := by
  classical
  let : DecidableEq (ULift.{w} ℕ) := Classical.decEq _
  let A := fun n : ULift.{w} ℕ ↦ X.obj n.down
  let d : (∐ A) ⟶ ∐ A := 𝟙 _ - Sigma.desc (fun n : ULift.{w} ℕ ↦
    X.map (homOfLE (Nat.le_succ n.down)) ≫ Sigma.ι A ⟨n.down + 1⟩)
  let T := Triangle.mk d q r
  have hT' : T ∈ distTriang C := hT
  have hc : ∀ n, X.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι A ⟨n + 1⟩ ≫ q =
      Sigma.ι A ⟨n⟩ ≫ q := by
    intro n
    have h := comp_distTriang_mor_zero₁₂ T hT'
    have hh := congrArg (fun t ↦ Sigma.ι A ⟨n⟩ ≫ t) h
    change Sigma.ι A ⟨n⟩ ≫ (d ≫ q) = _ at hh
    have hh' : Sigma.ι A ⟨n⟩ ≫ q =
        X.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι A ⟨n + 1⟩ ≫ q := by
      simpa [d, A, Category.assoc, Preadditive.comp_sub, Preadditive.sub_comp,
        sub_eq_zero] using hh
    exact hh'.symm
  have hn : ∀ (n m : ℕ) (h : n ≤ m),
      X.map (homOfLE h) ≫ Sigma.ι A ⟨m⟩ ≫ q = Sigma.ι A ⟨n⟩ ≫ q := by
    intro n m h
    induction m, h using Nat.le_induction with
    | base => simp
    | succ m h ih =>
      rw [show homOfLE (Nat.le_succ_of_le h) = homOfLE h ≫
        homOfLE (Nat.le_succ m) from rfl, X.map_comp, Category.assoc, hc m, ih]
  let c : Cocone (X ⋙ coyoneda.obj (op K)) :=
    { pt := K ⟶ Y
      ι :=
        { app n := ↾fun f ↦ f ≫ Sigma.ι A ⟨n⟩ ≫ q
          naturality := by
            intro n m a
            ext f
            change (f ≫ X.map a) ≫ Sigma.ι A ⟨m⟩ ≫ q =
              f ≫ Sigma.ι A ⟨n⟩ ≫ q
            rw [← homOfLE_leOfHom a, Category.assoc, hn n m (leOfHom a)] } }
  let φ : colimit (X ⋙ coyoneda.obj (op K)) → (K ⟶ Y) := colimit.desc _ c
  have hφ : ∀ n f, φ (colimit.ι (X ⋙ coyoneda.obj (op K)) n f) =
      f ≫ Sigma.ι A ⟨n⟩ ≫ q := by
    intro n f
    exact ConcreteCategory.congr_hom (colimit.ι_desc c n) f
  have hr : ∀ f : K ⟶ Y, f ≫ r = 0 := by
    intro f
    apply telescope_map_hom_zero K hK X (shiftFunctor C (1 : ℤ))
    have hz := comp_distTriang_mor_zero₃₁ T hT'
    change r ≫ (shiftFunctor C (1 : ℤ)).map d = 0 at hz
    change (f ≫ r) ≫ (shiftFunctor C (1 : ℤ)).map d = 0
    rw [Category.assoc, hz, comp_zero]
  have hsurj : Function.Surjective (fun f : K ⟶ ∐ A ↦ f ≫ q) := by
    intro f
    obtain ⟨g, hg⟩ := T.coyoneda_exact₃ hT' f (hr f)
    exact ⟨g, hg.symm⟩
  have hstage : ∀ g : K ⟶ ∐ A, ∃ (n : ℕ) (f : K ⟶ X.obj n),
      g ≫ q = f ≫ Sigma.ι A ⟨n⟩ ≫ q := by
    intro g
    let b := DirectSum.toAddMonoid (fun j ↦ Preadditive.rightComp K (Sigma.ι A j))
    have hb : ∀ x : DirectSum (ULift.{w} ℕ) (fun j ↦ (K ⟶ A j)),
        ∃ (n : ℕ) (f : K ⟶ X.obj n), b x ≫ q = f ≫ Sigma.ι A ⟨n⟩ ≫ q := by
      intro x
      induction x using DirectSum.induction_on with
      | zero => exact ⟨0, 0, by simp⟩
      | of j f => exact ⟨j.down, f, by simp [b, Preadditive.rightComp]⟩
      | add x y hx hy =>
        obtain ⟨n, f, hf⟩ := hx
        obtain ⟨m, g, hg⟩ := hy
        refine ⟨max n m, f ≫ X.map (homOfLE (le_max_left n m)) +
          g ≫ X.map (homOfLE (le_max_right n m)), ?_⟩
        simp only [map_add, Preadditive.add_comp, hf, hg, Category.assoc,
          hn n (max n m) (le_max_left n m), hn m (max n m) (le_max_right n m)]
    obtain ⟨x, rfl⟩ := (hK (ULift.{w} ℕ) A).2 g
    exact hb x
  refine ⟨φ, hφ, ?_, ?_⟩
  · intro x y hxy
    obtain ⟨n, f, rfl⟩ := Types.jointly_surjective' x
    obtain ⟨m, g, rfl⟩ := Types.jointly_surjective' y
    let k := max n m
    let f' := f ≫ X.map (homOfLE (le_max_left n m))
    let g' := g ≫ X.map (homOfLE (le_max_right n m))
    have he : (f' - g') ≫ Sigma.ι A ⟨k⟩ ≫ q = 0 := by
      rw [Preadditive.sub_comp]
      dsimp only [f', g', k]
      rw [Category.assoc, Category.assoc,
        hn n (max n m) (le_max_left n m), hn m (max n m) (le_max_right n m)]
      exact sub_eq_zero.mpr ((hφ n f).symm.trans (hxy.trans (hφ m g)))
    obtain ⟨a, ha⟩ := T.coyoneda_exact₂ hT' ((f' - g') ≫ Sigma.ι A ⟨k⟩)
      (by simpa [T, Category.assoc] using he)
    obtain ⟨l, hl, hzero⟩ := telescope_boundary_eventually_zero K hK X k (f' - g') a ha
    have heq : f' ≫ X.map (homOfLE hl) = g' ≫ X.map (homOfLE hl) := by
      simpa only [Preadditive.sub_comp, sub_eq_zero] using hzero
    apply Types.colimit_sound' (F := X ⋙ coyoneda.obj (op K)) (homOfLE ((le_max_left n m).trans hl))
      (homOfLE ((le_max_right n m).trans hl))
    change f ≫ X.map (homOfLE _) = g ≫ X.map (homOfLE _)
    simpa only [f', g', Category.assoc, ← X.map_comp, homOfLE_comp] using heq
  · intro f
    obtain ⟨g, hg⟩ := hsurj f
    obtain ⟨n, a, ha⟩ := hstage g
    exact ⟨colimit.ι (X ⋙ coyoneda.obj (op K)) n a, (hφ n a).trans (ha.symm.trans hg)⟩

end CategoryTheory
