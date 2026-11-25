/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.Telescope
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-! # The perfect-family calculation on a Brown telescope

Source: Krause, Derived categories, resolutions, and Brown representability, Section 4.5.
(blueprint: lem-sfb-perfect-family-telescope)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.Pretriangulated.Opposite
open CategoryTheory.BrownRepresentability

namespace CategoryTheory

section TowerSeparation

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [HasCoproducts.{v} C]

omit [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
private theorem sum_map_op {I : Type v} (X Y : I → C) (f : ∀ i, X i ⟶ Y i) :
    (Limits.Sigma.map f).op ≫ (opCoproductIsoProduct X).hom =
      (opCoproductIsoProduct Y).hom ≫ Limits.Pi.map (fun i ↦ (f i).op) := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, opCoproductIsoProduct_hom_comp_π, Pi.map_π]
  rw [← op_comp, Limits.Sigma.ι_map, op_comp]
  rw [← Category.assoc, opCoproductIsoProduct_hom_comp_π]

private theorem sum_weak_kernel {I : Type v} (T : I → Triangle C)
    (hT : ∀ i, T i ∈ distTriang C) {W : C}
    (f : W ⟶ ∐ fun i ↦ (T i).obj₂)
    (hf : f ≫ Limits.Sigma.map (fun i ↦ (T i).mor₂) = 0) :
    ∃ g : W ⟶ ∐ fun i ↦ (T i).obj₁,
      g ≫ Limits.Sigma.map (fun i ↦ (T i).mor₁) = f := by
  let U : I → Triangle Cᵒᵖ := fun i ↦ (triangleOpEquivalence C).functor.obj (op (T i))
  have hU : ∀ i, U i ∈ distTriang Cᵒᵖ := fun i ↦ op_distinguished (T i) (hT i)
  let V := productTriangle U
  have hV : V ∈ distTriang Cᵒᵖ := productTriangle_distinguished U hU
  let e₁ := opCoproductIsoProduct (fun i ↦ (T i).obj₁)
  let e₂ := opCoproductIsoProduct (fun i ↦ (T i).obj₂)
  let e₃ := opCoproductIsoProduct (fun i ↦ (T i).obj₃)
  let α : V.obj₂ ⟶ op W := e₂.inv ≫ f.op
  have hα : V.mor₁ ≫ α = 0 := by
    have h := sum_map_op (fun i ↦ (T i).obj₂) (fun i ↦ (T i).obj₃)
      (fun i ↦ (T i).mor₂)
    change (Limits.Sigma.map (fun i ↦ (T i).mor₂)).op ≫ e₂.hom =
      e₃.hom ≫ V.mor₁ at h
    apply (cancel_epi e₃.hom).1
    change e₃.hom ≫ (V.mor₁ ≫ (e₂.inv ≫ f.op)) = e₃.hom ≫ 0
    rw [comp_zero, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_assoc,
      ← op_comp, hf, op_zero]
  obtain ⟨γ, hγ⟩ := Triangle.yoneda_exact₂ V hV α hα
  refine ⟨(e₁.hom ≫ γ).unop, ?_⟩
  apply Quiver.Hom.op_inj
  rw [op_comp, Quiver.Hom.op_unop]
  have h := sum_map_op (fun i ↦ (T i).obj₁) (fun i ↦ (T i).obj₂)
    (fun i ↦ (T i).mor₁)
  change (Limits.Sigma.map (fun i ↦ (T i).mor₁)).op ≫ e₁.hom =
    e₂.hom ≫ V.mor₂ at h
  rw [← Category.assoc, h, Category.assoc, ← hγ]
  simp [α]

private theorem perfect_sum_kernel
    {J I : Type v} (S : J → C)
    (hperfect : ∀ (I : Type v) (X Y : I → C) (f : ∀ i, X i ⟶ Y i),
      (∀ i j, Function.Surjective (fun g : S j ⟶ X i ↦ g ≫ f i)) →
      ∀ j, Function.Surjective (fun g : S j ⟶ ∐ X ↦ g ≫ Limits.Sigma.map f))
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.Additive]
    (W W' : C) (z : H.obj (op W)) (c : W ⟶ W')
    (hkill : ∀ j (g : S j ⟶ W), H.map g.op z = 0 → g ≫ c = 0)
    (Y : I → C) (b : ∀ i, W ⟶ Y i) (y : ∀ i, H.obj (op (Y i)))
    (hb : ∀ i, H.map (b i).op (y i) = z)
    (j : J) (f : S j ⟶ ∐ fun _ : I ↦ W)
    (hf : f ≫ Limits.Sigma.map b = 0) :
    f ≫ Limits.Sigma.map (fun _ : I ↦ c) = 0 := by
  classical
  choose K k δ hT using fun i ↦ distinguished_cocone_triangle₁ (b i)
  let T : I → Triangle C := fun i ↦ Triangle.mk (k i) (b i) (δ i)
  obtain ⟨g, hg⟩ := sum_weak_kernel T hT f hf
  change S j ⟶ ∐ K at g
  change g ≫ Limits.Sigma.map k = f at hg
  let E (i : I) := Σ j, S j ⟶ K i
  let F (i : I) : E i → C := fun e ↦ S e.1
  let e (i : I) : (∐ F i) ⟶ K i := Sigma.desc fun e ↦ e.2
  have he (i : I) (j : J) : Function.Surjective (fun g : S j ⟶ ∐ F i ↦ g ≫ e i) := by
    intro g
    exact ⟨Sigma.ι (F i) ⟨j, g⟩, Sigma.ι_comp_desc _ _⟩
  obtain ⟨g', hg'⟩ := hperfect I (fun i ↦ ∐ F i) K e he j g
  change g' ≫ Limits.Sigma.map e = g at hg'
  rw [← hg, ← hg']
  simp only [Category.assoc]
  suffices h : Limits.Sigma.map e ≫ Limits.Sigma.map k ≫
      Limits.Sigma.map (fun _ : I ↦ c) = 0 by rw [h, comp_zero]
  apply Sigma.hom_ext
  intro i
  simp only [Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_map]
  have hi : e i ≫ k i ≫ c = 0 := by
    apply Sigma.hom_ext
    intro a
    simp only [e, Sigma.ι_comp_desc_assoc, comp_zero]
    rw [← Category.assoc]
    apply hkill a.1
    rw [← hb i, ← map_comp_apply]
    have hzero : k i ≫ b i = 0 := comp_distTriang_mor_zero₁₂ (T i) (hT i)
    rw [Category.assoc, hzero, comp_zero, op_zero, H.map_zero]
    rfl
  rw [← Category.assoc, ← Category.assoc, Category.assoc (e i) (k i) c, hi,
    zero_comp, comp_zero]

omit [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
private theorem constant_telescope_mono (W : C) :
    Mono (𝟙 (Telescope.sum (fun _ : ℕ ↦ W)) -
      Telescope.shift (fun _ : ℕ ↦ W) (fun _ ↦ 𝟙 W)) := by
  let Y : ℕ → C := fun _ ↦ W
  let d := Telescope.shift Y (fun _ ↦ 𝟙 W)
  let L : Telescope.sum Y ⟶ Telescope.sum Y :=
    Sigma.desc fun n : ULift.{v} ℕ ↦ - ∑ k ∈ Finset.range n.down, Telescope.ι Y k
  have hL : (𝟙 _ - d) ≫ L = 𝟙 _ := by
    apply Telescope.hom_ext
    intro n
    rw [← Category.assoc, Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp]
    dsimp only [d]
    rw [Telescope.ι_shift, Category.id_comp]
    simp only [L, Telescope.ι_desc, Finset.sum_range_succ]
    abel
  have : IsSplitMono (𝟙 _ - d) := ⟨⟨L, hL⟩⟩
  infer_instance

omit [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
private theorem constant_shift_mono (W : C) :
    Mono (Telescope.shift (fun _ : ℕ ↦ W) (fun _ ↦ 𝟙 W)) := by
  let Y : ℕ → C := fun _ ↦ W
  let L : Telescope.sum Y ⟶ Telescope.sum Y := Sigma.desc fun n : ULift.{v} ℕ ↦
    match n.down with
    | 0 => 0
    | k + 1 => Telescope.ι Y k
  have hL : Telescope.shift Y (fun _ ↦ 𝟙 W) ≫ L = 𝟙 _ := by
    apply Telescope.hom_ext
    intro n
    rw [← Category.assoc, Telescope.ι_shift, Category.id_comp, Category.comp_id]
    simp only [L, Telescope.ι_desc]
  have : IsSplitMono (Telescope.shift Y (fun _ ↦ 𝟙 W)) := ⟨⟨L, hL⟩⟩
  infer_instance

private theorem perfectFamily_tower_separation
    {J : Type v} (S : J → C)
    (hperfect : ∀ (I : Type v) (X Y : I → C) (f : ∀ i, X i ⟶ Y i),
      (∀ i j, Function.Surjective (fun g : S j ⟶ X i ↦ g ≫ f i)) →
      ∀ j, Function.Surjective (fun g : S j ⟶ ∐ X ↦ g ≫ Limits.Sigma.map f))
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.Additive]
    (X : ℕ → C) (a : ∀ n, X n ⟶ X (n + 1))
    (x : ∀ n, H.obj (op (X n)))
    (hx : ∀ n, H.map (a n).op (x (n + 1)) = x n)
    (hsurj : ∀ j, Function.Surjective (fun f : S j ⟶ X 0 ↦ H.map f.op (x 0)))
    (hkill : ∀ n j (f : S j ⟶ X n), H.map f.op (x n) = 0 → f ≫ a n = 0)
    (j : J) (f : S j ⟶ Telescope.sum X)
    (hf : f ≫ (𝟙 _ - Telescope.shift X a) = 0) : f = 0 := by
  classical
  let b : ∀ n, X 0 ⟶ X n :=
    fun n ↦ Nat.rec (𝟙 (X 0)) (fun n g ↦ g ≫ a n) n
  have hb (n : ℕ) : H.map (b n).op (x n) = x 0 := by
    induction n with
    | zero => simp [b]
    | succ n ih =>
      change H.map (b n ≫ a n).op (x (n + 1)) = x 0
      rw [map_comp_apply, hx, ih]
  let K (n : ℕ) := Σ j, {f : S j ⟶ X n // H.map f.op (x n) = 0}
  let F (n : ℕ) : K n → C := fun k ↦ S k.1
  let κ (n : ℕ) : (∐ F n) ⟶ X n := Sigma.desc fun k ↦ k.2.val
  let D (n : ℕ) := X 0 ⊞ ∐ F n
  let p (n : ℕ) : D n ⟶ X n := biprod.desc (b n) (κ n)
  have hp (n : ℕ) (j : J) : Function.Surjective (fun g : S j ⟶ D n ↦ g ≫ p n) := by
    intro f
    obtain ⟨g, hg⟩ := hsurj j (H.map f.op (x n))
    change H.map g.op (x 0) = H.map f.op (x n) at hg
    have hk : H.map (f - g ≫ b n).op (x n) = 0 := by
      rw [op_sub, H.map_sub]
      change H.map f.op (x n) - H.map (g ≫ b n).op (x n) = 0
      rw [map_comp_apply, hb, hg, sub_self]
    refine ⟨g ≫ biprod.inl + Sigma.ι (F n) ⟨j, f - g ≫ b n, hk⟩ ≫ biprod.inr, ?_⟩
    simp only [Preadditive.add_comp, Category.assoc, p, biprod.inl_desc,
      biprod.inr_desc, κ, Sigma.ι_comp_desc]
    exact add_sub_cancel _ _
  have hκa (n : ℕ) : κ n ≫ a n = 0 := by
    apply Sigma.hom_ext
    intro k
    simpa only [κ, Sigma.ι_comp_desc_assoc, comp_zero] using hkill n k.1 k.2.val k.2.property
  -- Compare the tower with the constant sequences at its first two stages.
  let Y₀ : ℕ → C := fun _ ↦ X 0
  let Y₁ : ℕ → C := fun _ ↦ X 1
  let s₀ := Telescope.shift Y₀ (fun _ ↦ 𝟙 _)
  let s₁ := Telescope.shift Y₁ (fun _ ↦ 𝟙 _)
  let B : Telescope.sum Y₀ ⟶ Telescope.sum X :=
    Limits.Sigma.map (fun n : ULift.{v} ℕ ↦ b n.down)
  let A₀ : Telescope.sum Y₀ ⟶ Telescope.sum Y₁ :=
    Limits.Sigma.map (fun _ : ULift.{v} ℕ ↦ a 0)
  let b₁ : ∀ n, X 1 ⟶ X (n + 1) :=
    fun n ↦ Nat.rec (𝟙 (X 1)) (fun n g ↦ g ≫ a (n + 1)) n
  have hb₁ (n : ℕ) : b (n + 1) = a 0 ≫ b₁ n := by
    induction n with
    | zero => simp [b, b₁]
    | succ n ih =>
      change b (n + 1) ≫ a (n + 1) = a 0 ≫ (b₁ n ≫ a (n + 1))
      rw [ih, Category.assoc]
  let c₁ : Telescope.sum Y₁ ⟶ Telescope.sum X :=
    Sigma.desc fun n : ULift.{v} ℕ ↦ b₁ n.down ≫ Telescope.ι X (n.down + 1)
  have hBd : B ≫ Telescope.shift X a = s₀ ≫ B := by
    apply Telescope.hom_ext
    intro n
    have hBn (n : ℕ) : Telescope.ι Y₀ n ≫ B = b n ≫ Telescope.ι X n :=
      Limits.Sigma.ι_map _ _
    dsimp only [s₀]
    rw [← Category.assoc, hBn, Category.assoc, Telescope.ι_shift,
      Telescope.ι_shift_assoc, Category.id_comp, hBn]
    exact (Category.assoc _ _ _).symm
  have hAs : s₀ ≫ A₀ = A₀ ≫ s₁ := by
    apply Telescope.hom_ext
    intro n
    have hAn (n : ℕ) : Telescope.ι Y₀ n ≫ A₀ = a 0 ≫ Telescope.ι Y₁ n :=
      Limits.Sigma.ι_map _ _
    dsimp only [s₀, s₁]
    rw [Telescope.ι_shift_assoc, Category.id_comp, hAn,
      ← Category.assoc, hAn, Category.assoc, Telescope.ι_shift, Category.id_comp]
  have hBc : s₀ ≫ B = A₀ ≫ c₁ := by
    apply Telescope.hom_ext
    intro n
    dsimp only [s₀, s₁]
    rw [Telescope.ι_shift_assoc, Category.id_comp]
    rw [← Category.assoc]
    change Sigma.ι _ (ULift.up (n + 1)) ≫ B =
      (Sigma.ι _ (ULift.up n) ≫ A₀) ≫ c₁
    rw [Limits.Sigma.ι_map, Limits.Sigma.ι_map]
    change b (n + 1) ≫ Telescope.ι X (n + 1) =
      (a 0 ≫ Sigma.ι (fun _ : ULift.{v} ℕ ↦ X 1) (ULift.up n)) ≫ c₁
    simpa only [Category.assoc, c₁, Sigma.ι_comp_desc] using
      congrArg (fun k ↦ k ≫ Telescope.ι X (n + 1)) (hb₁ n)
  have hpa (n : ℕ) : p n ≫ a n = biprod.fst ≫ b (n + 1) := by
    apply biprod.hom_ext'
    · simp only [p, biprod.inl_desc_assoc, biprod.inl_fst_assoc]
      rfl
    · simp only [p, biprod.inr_desc_assoc, biprod.inr_fst_assoc, hκa, zero_comp]
  let D' : ULift.{v} ℕ → C := fun n ↦ D n.down
  let ps : (∐ D') ⟶ Telescope.sum X := Limits.Sigma.map (fun n ↦ p n.down)
  let c₀ : (∐ D') ⟶ Telescope.sum Y₀ :=
    Sigma.desc fun n : ULift.{v} ℕ ↦ biprod.fst ≫ Telescope.ι Y₀ n.down
  have hps : ps ≫ Telescope.shift X a = c₀ ≫ s₀ ≫ B := by
    apply Sigma.hom_ext
    intro n
    dsimp only [ps]
    rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc]
    change p n.down ≫ Telescope.ι X n.down ≫ Telescope.shift X a = _
    rw [Telescope.ι_shift, ← Category.assoc, hpa, Category.assoc]
    dsimp only [c₀, s₀]
    rw [Sigma.ι_comp_desc_assoc]
    simp only [Category.assoc, Telescope.ι_shift_assoc, Category.id_comp]
    change _ = biprod.fst ≫ (Sigma.ι _ (ULift.up (n.down + 1)) ≫ B)
    dsimp only [B]
    rw [Limits.Sigma.ι_map]
    rfl
  obtain ⟨g, hg⟩ := hperfect (ULift.{v} ℕ) D' (fun n ↦ X n.down)
    (fun n ↦ p n.down) (fun n j ↦ hp n.down j) j f
  change g ≫ ps = f at hg
  have hfix : f = f ≫ Telescope.shift X a := by
    simpa only [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] using hf
  let u := g ≫ c₀
  let h := u ≫ s₀
  have hfB : f = h ≫ B := by
    rw [hfix, ← hg, Category.assoc, hps]
    simp only [h, u, Category.assoc]
  have hkernel : (h - h ≫ s₀) ≫ B = 0 := by
    rw [Preadditive.sub_comp]
    have hs : (h ≫ s₀) ≫ B = f ≫ Telescope.shift X a := by
      rw [Category.assoc, ← hBd, ← Category.assoc, ← hfB]
    rw [hs, ← hfB, ← hfix, sub_self]
  have hA : (h - h ≫ s₀) ≫ A₀ = 0 :=
    perfect_sum_kernel S hperfect H (X 0) (X 1) (x 0) (a 0) (hkill 0)
      (fun n : ULift.{v} ℕ ↦ X n.down) (fun n ↦ b n.down)
      (fun n ↦ x n.down) (fun n ↦ hb n.down) j (h - h ≫ s₀) hkernel
  have hh : h ≫ A₀ = 0 := by
    have := constant_telescope_mono (X 1)
    apply (cancel_mono (𝟙 _ - s₁)).1
    rw [zero_comp, Preadditive.comp_sub, Category.comp_id]
    simpa only [Preadditive.sub_comp, Category.assoc, hAs] using hA
  have hu : u ≫ A₀ = 0 := by
    have := constant_shift_mono (X 1)
    apply (cancel_mono s₁).1
    rw [zero_comp]
    simpa only [h, Category.assoc, hAs] using hh
  rw [hfB]
  change (u ≫ s₀) ≫ B = 0
  rw [Category.assoc, hBc, ← Category.assoc, hu, zero_comp]

end TowerSeparation

/-- A compatible telescope element is universal on a perfect family if the initial
stage surjects and each transition kills the preceding kernel.

Source: Krause, *Derived categories, resolutions, and Brown representability*,
Section 4.5, the lemma on coherent functors and the comparison of (4.1) with the
telescope triangle; Krause, *Localization theory for triangulated categories*, 5.1.1.
(blueprint: lem-sfb-perfect-family-telescope)

Proof: cover each X n by X 0 plus the evaluation coproduct of generator maps
in the kernel of its element. Perfectness lifts generator maps into the sum of X n
through the sum of these covers. Since every kernel summand dies at the next stage,
its composite to the telescope vanishes. Consequently, any generator map which
lifts through the telescope projection factors through X 0.

For the lifting, prove that identity minus the transition is injective on generator
maps into the sum. If f is fixed by the transition, use the preceding covers to
factor it through the sum of copies of X 0. Perfectness and coproducts of weak
kernels show that the difference from its constant-sequence shift is killed by the
sum of the first transition a 0. Both shift and identity-minus-shift on a constant
sequence are split monomorphisms, with explicit retractions. Cancelling these
monomorphisms makes f zero. Shift closure and exactness of the telescope triangle
now give the required lifting. Surjectivity follows from the initial stage;
injectivity follows because its kernel is killed by a 0.
-/
theorem perfectFamily_telescope_bijective
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [HasCoproducts.{v} C]
    {J : Type v} (S : J → C)
    (hshift : ∀ (j : J) (n : ℤ), ∃ k, Nonempty (S k ≅ (S j)⟦n⟧))
    (hperfect : ∀ (I : Type v) (X Y : I → C) (f : ∀ i, X i ⟶ Y i),
      (∀ i j, Function.Surjective (fun g : S j ⟶ X i ↦ g ≫ f i)) →
      ∀ j, Function.Surjective (fun g : S j ⟶ ∐ X ↦ g ≫ Limits.Sigma.map f))
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.Additive]
    (X : ℕ → C) (a : ∀ n, X n ⟶ X (n + 1))
    (x : ∀ n, H.obj (op (X n)))
    (hx : ∀ n, H.map (a n).op (x (n + 1)) = x n)
    (hsurj : ∀ j, Function.Surjective (fun f : S j ⟶ X 0 ↦ H.map f.op (x 0)))
    (hkill : ∀ n j (f : S j ⟶ X n), H.map f.op (x n) = 0 → f ≫ a n = 0)
    (T : C) (q : Telescope.sum X ⟶ T) (r : T ⟶ (Telescope.sum X)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (𝟙 _ - Telescope.shift X a) q r ∈ distTriang C)
    (t : H.obj (op T))
    (ht : ∀ n, H.map (Telescope.ι X n ≫ q).op t = x n) :
    ∀ j, Function.Bijective (fun f : S j ⟶ T ↦ H.map f.op t) := by
  classical
  let b : ∀ n, X 0 ⟶ X n :=
    fun n ↦ Nat.rec (𝟙 (X 0)) (fun n g ↦ g ≫ a n) n
  have hb (n : ℕ) : H.map (b n).op (x n) = x 0 := by
    induction n with
    | zero => simp [b]
    | succ n ih =>
      change H.map (b n ≫ a n).op (x (n + 1)) = x 0
      rw [map_comp_apply, hx, ih]
  have hbq (n : ℕ) : b n ≫ Telescope.ι X n ≫ q = Telescope.ι X 0 ≫ q := by
    induction n with
    | zero => simp [b]
    | succ n ih =>
      change (b n ≫ a n) ≫ Telescope.ι X (n + 1) ≫ q = _
      rw [Category.assoc, ← Telescope.ι_π hT n, ih]
  let K (n : ℕ) := Σ j, {f : S j ⟶ X n // H.map f.op (x n) = 0}
  let F (n : ℕ) : K n → C := fun k ↦ S k.1
  let κ (n : ℕ) : (∐ F n) ⟶ X n := Sigma.desc fun k ↦ k.2.val
  let D (n : ℕ) := X 0 ⊞ ∐ F n
  let p (n : ℕ) : D n ⟶ X n := biprod.desc (b n) (κ n)
  have hp (n : ℕ) (j : J) : Function.Surjective (fun g : S j ⟶ D n ↦ g ≫ p n) := by
    intro f
    obtain ⟨g, hg⟩ := hsurj j (H.map f.op (x n))
    change H.map g.op (x 0) = H.map f.op (x n) at hg
    have hk : H.map (f - g ≫ b n).op (x n) = 0 := by
      rw [op_sub, H.map_sub]
      change H.map f.op (x n) - H.map (g ≫ b n).op (x n) = 0
      rw [map_comp_apply, hb, hg, sub_self]
    refine ⟨g ≫ biprod.inl + Sigma.ι (F n) ⟨j, f - g ≫ b n, hk⟩ ≫ biprod.inr, ?_⟩
    simp only [Preadditive.add_comp, Category.assoc, p, biprod.inl_desc,
      biprod.inr_desc, κ, Sigma.ι_comp_desc]
    exact add_sub_cancel _ _
  have hκa (n : ℕ) : κ n ≫ a n = 0 := by
    apply Sigma.hom_ext
    intro k
    simpa only [κ, Sigma.ι_comp_desc_assoc, comp_zero] using hkill n k.1 k.2.val k.2.property
  have hκq (n : ℕ) : κ n ≫ Telescope.ι X n ≫ q = 0 := by
    rw [Telescope.ι_π hT n, ← Category.assoc, hκa, zero_comp]
  have hpq (n : ℕ) : p n ≫ Telescope.ι X n ≫ q = biprod.fst ≫ Telescope.ι X 0 ≫ q := by
    apply biprod.hom_ext'
    · simp only [p, biprod.inl_desc_assoc, biprod.inl_fst_assoc, hbq]
    · simp only [p, biprod.inr_desc_assoc, biprod.inr_fst_assoc,
        hκq, zero_comp]
  let D' : ULift.{v} ℕ → C := fun n ↦ D n.down
  let X' : ULift.{v} ℕ → C := fun n ↦ X n.down
  let ps : (∐ D') ⟶ ∐ X' := Limits.Sigma.map (fun n ↦ p n.down)
  let c : (∐ D') ⟶ X 0 := Sigma.desc (fun _ ↦ biprod.fst)
  have hps (j : J) : Function.Surjective (fun g : S j ⟶ ∐ D' ↦ g ≫ ps) :=
    hperfect _ D' X' (fun n ↦ p n.down) (fun n j ↦ hp n.down j) j
  have hpsq : ps ≫ q = c ≫ Telescope.ι X 0 ≫ q := by
    apply Sigma.hom_ext
    intro n
    dsimp only [ps, c]
    simp only [Limits.Sigma.ι_map_assoc, Sigma.ι_comp_desc_assoc]
    exact hpq n.down
  have hfactor (j : J) (f : S j ⟶ T) :
      ∃ g : S j ⟶ X 0, f = g ≫ Telescope.ι X 0 ≫ q := by
    have hfr : f ≫ r = 0 := by
      obtain ⟨k, ⟨e⟩⟩ := hshift j (-1)
      apply eq_zero_of_comp_shift_eq_zero e (𝟙 _ - Telescope.shift X a)
        (fun g hg ↦ perfectFamily_tower_separation S hperfect H X a x hx hsurj hkill
          k g hg)
      have h := comp_distTriang_mor_zero₃₁ _ hT
      change r ≫ (𝟙 _ - Telescope.shift X a)⟦(1 : ℤ)⟧' = 0 at h
      rw [Category.assoc, h, comp_zero]
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₃ _ hT f hfr
    change f = g ≫ q at hg
    obtain ⟨g', hg'⟩ := hps j g
    change g' ≫ ps = g at hg'
    refine ⟨g' ≫ c, ?_⟩
    rw [hg, ← hg', Category.assoc, hpsq]
    simp only [Category.assoc]
  intro j
  have hkernel (f : S j ⟶ T) (hf : H.map f.op t = 0) : f = 0 := by
    obtain ⟨g, rfl⟩ := hfactor j f
    rw [map_comp_apply, ht 0] at hf
    have hg := hkill 0 j g hf
    rw [Telescope.ι_π hT 0, ← Category.assoc, hg, zero_comp]
  constructor
  · intro f g hfg
    apply sub_eq_zero.mp
    apply hkernel
    rw [op_sub, H.map_sub]
    exact sub_eq_zero.mpr hfg
  · intro z
    obtain ⟨f, hf⟩ := hsurj j z
    change H.map f.op (x 0) = z at hf
    refine ⟨f ≫ Telescope.ι X 0 ≫ q, ?_⟩
    change H.map (f ≫ Telescope.ι X 0 ≫ q).op t = z
    rw [map_comp_apply, ht 0, hf]

end CategoryTheory
