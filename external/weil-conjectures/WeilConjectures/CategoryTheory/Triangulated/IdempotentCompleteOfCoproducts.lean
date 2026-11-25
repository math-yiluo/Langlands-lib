/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.Telescope

/-!
# Pretriangulated categories with countable coproducts are idempotent complete

Let `C` be a pretriangulated category with coproducts indexed by `Type w`, for any universe `w`.
Then `C` is idempotent complete
(`CategoryTheory.Pretriangulated.isIdempotentComplete_of_hasCoproducts`, Bökstedt–Neeman, Stacks
Tag 05QW, blueprint `lemma-hypotheses-brown-representability`). Only the countable coproduct `∐ₙ A`,
indexed by `ULift.{w} ℕ`, is used.

For an idempotent `e : A ⟶ A`, let `Z` be the telescope (homotopy colimit) of
`A ⟶[e] A ⟶[e] A ⟶ ⋯`, the third object of a distinguished triangle
`∐ₙ A ⟶[𝟙 - t] ∐ₙ A ⟶[π] Z ⟶ (∐ₙ A)⟦1⟧`. Precomposition with `𝟙 - t` is surjective on morphisms
out of `∐ₙ A` (`CategoryTheory.Pretriangulated.IdempotentTelescope.exists_comp_eq`), so `π` is
an epimorphism, and `Z` is an image of `e`: the maps `A ⟶ Z` (via the summand `0`) and
`Z ⟶ A` (induced by `e` on each summand) split `e`. These telescope lemmas use the coproducts
indexed by `Type v`. The theorem itself allows any coproduct universe `w`: it splits `e` through
the cone of a split monomorphism `∐ₙ A ⟶ ∐ₙ A`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Category Preadditive

namespace CategoryTheory.Pretriangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

namespace IdempotentTelescope

variable [HasCoproducts.{v} C]

open BrownRepresentability Telescope

variable {A : C} {e : A ⟶ A} (he : e ≫ e = e)
include he

omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- For an idempotent `e : A ⟶ A`, precomposition with `𝟙 - t` is surjective on morphisms out of
`∐ₙ A`, where `t` is the shift of the sequence `A ⟶[e] A ⟶[e] ⋯`: a family `hₙ : A ⟶ W` is the
image of `gₙ = (𝟙 - e) ≫ hₙ - ∑_{j < n} e ≫ hⱼ`. -/
lemma exists_comp_eq {W : C} (h : sum (fun _ : ℕ ↦ A) ⟶ W) :
    ∃ g, (𝟙 _ - shift (fun _ : ℕ ↦ A) (fun _ ↦ e)) ≫ g = h := by
  refine ⟨Sigma.desc fun k ↦ (𝟙 A - e) ≫ ι (fun _ : ℕ ↦ A) k.down ≫ h -
    ∑ j ∈ Finset.range k.down, e ≫ ι (fun _ : ℕ ↦ A) j ≫ h, ?_⟩
  refine hom_ext _ fun n ↦ ?_
  rw [sub_comp, comp_sub, id_comp, ι_shift_assoc, ι_desc, ι_desc]
  simp only [comp_sub, comp_add, comp_sum, Finset.sum_range_succ, ← assoc, he, sub_comp, id_comp,
    sub_self]
  abel


variable {Z : C} {π : sum (fun _ : ℕ ↦ A) ⟶ Z} {δ : Z ⟶ (sum (fun _ : ℕ ↦ A))⟦(1 : ℤ)⟧}
  (hT : Triangle.mk (𝟙 _ - shift (fun _ : ℕ ↦ A) (fun _ ↦ e)) π δ ∈ distTriang C)
include hT

/-- The map `π : ∐ₙ A ⟶ Z` to the telescope of an idempotent is an epimorphism. -/
lemma epi_π : Epi π := by
  refine ⟨fun {W} u₁ u₂ hu ↦ ?_⟩
  rw [← sub_eq_zero]
  have hu' : π ≫ (u₁ - u₂) = 0 := by rw [comp_sub, hu, sub_self]
  obtain ⟨h, hh⟩ : ∃ h : (sum (fun _ : ℕ ↦ A))⟦(1 : ℤ)⟧ ⟶ W, u₁ - u₂ = δ ≫ h :=
    Triangle.yoneda_exact₃ _ hT (u₁ - u₂) hu'
  let adj := (shiftEquiv' C (1 : ℤ) (-1) (by norm_num)).toAdjunction
  obtain ⟨g, hg⟩ := exists_comp_eq he (adj.homEquiv _ _ h)
  have : h = (𝟙 _ - shift (fun _ : ℕ ↦ A) (fun _ ↦ e))⟦(1 : ℤ)⟧' ≫
      (adj.homEquiv _ _).symm g := by
    have := adj.homEquiv_naturality_left_symm (𝟙 _ - shift (fun _ : ℕ ↦ A) (fun _ ↦ e)) g
    rw [hg, Equiv.symm_apply_apply] at this
    exact this
  have h₀ : δ ≫ (𝟙 _ - shift (fun _ : ℕ ↦ A) (fun _ ↦ e))⟦(1 : ℤ)⟧' = 0 :=
    comp_distTriang_mor_zero₃₁ _ hT
  rw [hh, this, ← assoc, h₀, zero_comp]

/-- In the telescope of an idempotent `e`, the maps `A ⟶ Z` from the summands are invariant
under `e`. -/
lemma e_comp_ι_π (n : ℕ) : e ≫ ι (fun _ : ℕ ↦ A) n ≫ π = ι (fun _ : ℕ ↦ A) n ≫ π := by
  rw [ι_π hT n, ← assoc, he]

/-- In the telescope of an idempotent, all the maps `A ⟶ Z` from the summands agree. -/
lemma ι_π_eq (n : ℕ) : ι (fun _ : ℕ ↦ A) n ≫ π = ι (fun _ : ℕ ↦ A) 0 ≫ π := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← ih, ι_π hT n, e_comp_ι_π he hT]

/-- The telescope `Z` of an idempotent `e : A ⟶ A` is an image of `e`: there are `r : Z ⟶ A`
and `i : A ⟶ Z` with `r ≫ i = 𝟙 Z` and `i ≫ r = e`. -/
lemma exists_split : ∃ (r : Z ⟶ A) (i : A ⟶ Z), r ≫ i = 𝟙 Z ∧ i ≫ r = e := by
  have := epi_π he hT
  let g : sum (fun _ : ℕ ↦ A) ⟶ A := Sigma.desc fun _ ↦ e
  have hg : (𝟙 _ - shift (fun _ : ℕ ↦ A) (fun _ ↦ e)) ≫ g = 0 := by
    refine hom_ext _ fun n ↦ ?_
    simp [g, he]
  obtain ⟨r, hr⟩ : ∃ r : Z ⟶ A, g = π ≫ r := Triangle.yoneda_exact₂ _ hT g hg
  refine ⟨r, ι (fun _ : ℕ ↦ A) 0 ≫ π, ?_, ?_⟩
  · rw [← cancel_epi π, ← assoc, ← hr, comp_id]
    refine hom_ext _ fun n ↦ ?_
    rw [ι_desc_assoc, ι_π_eq he hT n, e_comp_ι_π he hT]
  · rw [assoc, ← hr, ι_desc]


end IdempotentTelescope

/-- A pretriangulated category with coproducts indexed by `Type w` is idempotent complete
(Bökstedt–Neeman, Stacks Tag 05QW).

Proof: let `p : X ⟶ X` be idempotent, `q = 𝟙 - p`, and `S = ∐ₙ X` (indexed by `ULift.{w} ℕ`).
The map `φ : S ⟶ S` sending the summand `n` by `q` to the summand `n` plus by `p` to the summand
`n + 1` is a split monomorphism, so in a distinguished triangle `S ⟶[φ] S ⟶[a] G ⟶ S⟦1⟧` the
third map vanishes and `a` is an epimorphism. The map `c : S ⟶ X` which is `p` on the summand `0`
and zero elsewhere kills `φ`, so it factors as `a ≫ i`; then `i : G ⟶ X` and the composite of the
summand `0` with `a` split `p`. -/
theorem isIdempotentComplete_of_hasCoproducts [HasCoproducts.{w} C] : IsIdempotentComplete C := by
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


end CategoryTheory.Pretriangulated
