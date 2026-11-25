/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Countable coproducts and idempotent completeness

Source: Stacks Project, Tag 05QW, `derived-lemma-countable-products-karoubian`.
-/

@[expose] public section

universe w v u

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- A pretriangulated category admitting countable coproducts is idempotent complete.
Source: Stacks Project, Tag 05QW, Lemma 13.4.14, coproduct assertion.
(blueprint: lem-countable-coproducts-idempotent-complete)

Proof in words: the opposite category has countable products. To split an
idempotent in an additive category with countable products it suffices to have
kernels for split epimorphisms (the countable-product criterion of Stacks Tag 05QV).
In a pretriangulated category every epimorphism has a kernel: complete the map
to a distinguished triangle and rotate once, then apply the exact Hom sequences;
the connecting map is zero because the original map is epic, and exactness gives
the kernel universal property. Apply this criterion to the opposite category,
then take opposites of the splitting maps. The coproduct is indexed by ULift ℕ
so that the statement works in an arbitrary indexing universe w. -/
theorem isIdempotentComplete_of_countableCoproducts
    (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasCoproducts.{w} C] : IsIdempotentComplete C := by
  classical
  constructor
  intro X p hp
  let q : X ⟶ X := 𝟙 X - p
  have hqq : q ≫ q = q := Idempotents.idem_of_id_sub_idem p hp
  have hpq : p ≫ q = 0 := by simp [q, Preadditive.comp_sub, hp]
  have hqp : q ≫ p = 0 := by simp [q, Preadditive.sub_comp, hp]
  let A : ULift.{w} ℕ → C := fun _ => X
  let S := ∐ A
  let ι : ℕ → (X ⟶ S) := fun n => Sigma.ι A ⟨n⟩
  let φ : S ⟶ S := Sigma.desc fun n : ULift.{w} ℕ =>
    q ≫ ι n.down + p ≫ ι (n.down + 1)
  let ψ : S ⟶ S := Sigma.desc fun n : ULift.{w} ℕ =>
    match n.down with
    | 0 => ι 0
    | k + 1 => p ≫ ι k + q ≫ ι (k + 1)
  have hφ (n : ℕ) : ι n ≫ φ = q ≫ ι n + p ≫ ι (n + 1) := by
    dsimp [ι, φ]
    simp only [Sigma.ι_comp_desc]
  have hψ₀ : ι 0 ≫ ψ = ι 0 := by
    dsimp [ι, ψ]
    simp only [Sigma.ι_comp_desc]
  have hψ (n : ℕ) : ι (n + 1) ≫ ψ = p ≫ ι n + q ≫ ι (n + 1) := by
    dsimp [ι, ψ]
    simp only [Sigma.ι_comp_desc]
  have hφψ : φ ≫ ψ = 𝟙 S := by
    apply Sigma.hom_ext
    intro n
    change ι n.down ≫ (φ ≫ ψ) = ι n.down ≫ 𝟙 S
    rw [← Category.assoc, hφ, Preadditive.add_comp, Category.assoc,
      Category.assoc, hψ]
    cases hn : n.down with
    | zero =>
      rw [hψ₀]
      simp only [Preadditive.comp_add, ← Category.assoc, hp, hpq,
        zero_comp, add_zero, Category.comp_id]
      simp only [q, Preadditive.sub_comp, Category.id_comp, sub_add_cancel]
    | succ k =>
      rw [hψ k]
      simp only [Preadditive.comp_add, ← Category.assoc, hp, hqq, hpq, hqp,
        zero_comp, add_zero, zero_add, Category.comp_id]
      simp only [q, Preadditive.sub_comp, Category.id_comp, sub_add_cancel]
  have : IsSplitMono φ := ⟨⟨ψ, hφψ⟩⟩
  obtain ⟨G, a, b, hT⟩ := Pretriangulated.distinguished_cocone_triangle φ
  let T := Triangle.mk φ a b
  have hT' : T ∈ distTriang C := hT
  have hb : b = 0 := T.mor₃_eq_zero_of_mono₁ hT' (inferInstanceAs (Mono φ))
  have : Epi a := T.epi₂ hT' hb
  have hφa : φ ≫ a = 0 := Pretriangulated.comp_distTriang_mor_zero₁₂ T hT'
  let c : S ⟶ X := Sigma.desc fun n : ULift.{w} ℕ =>
    match n.down with
    | 0 => p
    | _ + 1 => 0
  have hc₀ : ι 0 ≫ c = p := by dsimp [ι, c]; simp only [Sigma.ι_comp_desc]
  have hc (n : ℕ) : ι (n + 1) ≫ c = 0 := by
    dsimp [ι, c]
    simp only [Sigma.ι_comp_desc]
  have hφc : φ ≫ c = 0 := by
    apply Sigma.hom_ext
    intro n
    change ι n.down ≫ (φ ≫ c) = ι n.down ≫ 0
    rw [← Category.assoc, hφ, Preadditive.add_comp, Category.assoc,
      Category.assoc, hc, comp_zero, add_zero, comp_zero]
    cases hn : n.down with
    | zero => rw [hc₀, hqp]
    | succ k => rw [hc k, comp_zero]
  obtain ⟨i, hi⟩ := T.yoneda_exact₂ hT' c hφc
  change c = a ≫ i at hi
  have hrel (n : ℕ) : q ≫ ι n ≫ a + p ≫ ι (n + 1) ≫ a = 0 := by
    have h := congrArg (fun f => ι n ≫ f) hφa
    simpa only [← Category.assoc, hφ, Preadditive.add_comp, comp_zero] using h
  have hqa (n : ℕ) : q ≫ ι n ≫ a = 0 := by
    have h := congrArg (fun f => q ≫ f) (hrel n)
    simpa only [Preadditive.comp_add, ← Category.assoc, hqq, hqp,
      zero_comp, add_zero, comp_zero] using h
  have hpa (n : ℕ) : p ≫ ι (n + 1) ≫ a = 0 := by
    simpa only [hqa n, zero_add] using hrel n
  have ha (n : ℕ) : ι (n + 1) ≫ a = 0 := by
    have h := congrArg (fun f => f ≫ ι (n + 1) ≫ a)
      (show q + p = 𝟙 X by simp [q])
    simpa only [Preadditive.add_comp, Category.id_comp, hqa, hpa,
      add_zero] using h.symm
  refine ⟨G, i, ι 0 ≫ a, ?_, ?_⟩
  · apply (cancel_epi a).1
    rw [Category.comp_id, ← Category.assoc, ← hi]
    apply Sigma.hom_ext
    intro n
    change ι n.down ≫ (c ≫ (ι 0 ≫ a)) = ι n.down ≫ a
    rw [← Category.assoc]
    cases hn : n.down with
    | zero =>
      rw [hc₀]
      have h := hqa 0
      have heq : ι 0 ≫ a = p ≫ ι 0 ≫ a := sub_eq_zero.mp (by
        simpa only [q, Preadditive.sub_comp, Category.id_comp, Category.assoc] using h)
      exact heq.symm
    | succ k => rw [hc k, zero_comp, ha k]
  · rw [Category.assoc, ← hi, hc₀]

end CategoryTheory
