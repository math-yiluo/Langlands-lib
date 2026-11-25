/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# `ℓ`-adic towers in abelian categories

An `ℓ`-adic tower in an abelian category `C` (`CategoryTheory.AdicTowerStructure`) is a tower
`(Gₙ)` together with maps `ιₙₘ : Gₙ ⟶ Gₙ₊ₘ` such that `0 ⟶ Gₙ ⟶ Gₙ₊ₘ ⟶ Gₘ ⟶ 0` (the second map
being the transition map) is short exact, and such that the transition map `Gₙ₊ₘ ⟶ Gₙ` followed
by `ιₙₘ` is multiplication by `ℓᵐ`.

Such a structure exists (`CategoryTheory.AdicTowerStructure.ofIsColimit`) on a tower `(Gₙ)` with
`ℓⁿ Gₙ = 0` whose transition maps `G_k ⟶ Gₙ` are cokernels of `ℓⁿ : G_k ⟶ G_k` (that is,
`G_k ⊗ ℤ/ℓⁿ ≅ Gₙ`) and which is flat (`G_{n+m} --ℓⁿ--> G_{n+m} --ℓᵐ--> G_{n+m}` is exact): for
instance a tower of flat sheaves of `ℤ/ℓⁿ`-modules `Fₙ` with `Fₙ₊₁ ⊗ ℤ/ℓⁿ ≅ Fₙ`. Then `ιₙₘ` is
induced by multiplication by `ℓᵐ`.
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type*} [Category C] [Abelian C]

/-- An **`ℓ`-adic tower structure** on a tower `(Gₙ)` of an abelian category: maps
`ιₙₘ : Gₙ ⟶ Gₙ₊ₘ` with `0 ⟶ Gₙ ⟶ Gₙ₊ₘ ⟶ Gₘ ⟶ 0` short exact (the second map being the
transition map) and such that the transition map `Gₙ₊ₘ ⟶ Gₙ` followed by `ιₙₘ` is `ℓᵐ`. -/
structure AdicTowerStructure (G : ℕᵒᵖ ⥤ C) (ℓ : ℕ) where
  /-- The map `Gₙ ⟶ Gₙ₊ₘ`, "multiplication by `ℓᵐ`". -/
  ι (n m : ℕ) : G.obj (op n) ⟶ G.obj (op (n + m))
  map_ι (n m : ℕ) : G.map (homOfLE (Nat.le_add_right n m)).op ≫ ι n m = ℓ ^ m • 𝟙 _
  ι_map (n m : ℕ) : ι n m ≫ G.map (homOfLE (Nat.le_add_left m n)).op = 0
  shortExact (n m : ℕ) : (ShortComplex.mk _ _ (ι_map n m)).ShortExact

namespace AdicTowerStructure

variable {G : ℕᵒᵖ ⥤ C} {ℓ : ℕ}

/-- The transition maps of an `ℓ`-adic tower are epimorphisms. -/
lemma epi_map (A : AdicTowerStructure G ℓ) {n k : ℕ} (h : n ≤ k) :
    Epi (G.map (homOfLE h).op) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' h
  exact (A.shortExact d n).epi_g

/-- `ιₙₘ` followed by the transition map `Gₙ₊ₘ ⟶ Gₙ` is `ℓᵐ`. -/
lemma ι_comp_map (A : AdicTowerStructure G ℓ) (n m : ℕ) :
    A.ι n m ≫ G.map (homOfLE (Nat.le_add_right n m)).op = ℓ ^ m • 𝟙 _ := by
  have := A.epi_map (Nat.le_add_right n m)
  rw [← cancel_epi (G.map (homOfLE (Nat.le_add_right n m)).op), ← Category.assoc, A.map_ι,
    Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]

/-- `ℓⁿ` kills `Gₙ`: `ℓⁿ = ιₙₙ ≫ (G₂ₙ ⟶ Gₙ)` and `ιₙₙ` composed with the transition map
`G₂ₙ ⟶ Gₙ` vanishes. -/
lemma pow_smul_id_eq_zero (A : AdicTowerStructure G ℓ) (n : ℕ) :
    ℓ ^ n • 𝟙 (G.obj (op n)) = 0 := by
  rw [← A.ι_comp_map n n]
  exact A.ι_map n n

/-- Naturality of `ιₙₘ` in `n`. -/
lemma map_comp_ι (A : AdicTowerStructure G ℓ) {n k : ℕ} (m : ℕ) (h : n ≤ k) :
    G.map (homOfLE h).op ≫ A.ι n m =
      A.ι k m ≫ G.map (homOfLE (Nat.add_le_add_right h m)).op := by
  have := A.epi_map (Nat.le_add_right k m)
  rw [← cancel_epi (G.map (homOfLE (Nat.le_add_right k m)).op), ← Category.assoc,
    ← G.map_comp, ← Category.assoc, A.map_ι, Linear.smul_comp, Category.id_comp]
  have e : (homOfLE (Nat.le_add_right k m)).op ≫ (homOfLE h).op =
      (homOfLE (Nat.add_le_add_right h m)).op ≫ (homOfLE (Nat.le_add_right n m)).op :=
    Subsingleton.elim _ _
  rw [e, G.map_comp, Category.assoc, A.map_ι, Linear.comp_smul, Category.comp_id]

/-- The short exact sequence `0 ⟶ Gₙ ⟶ Gₙ₊ₘ ⟶ Gₘ ⟶ 0`. -/
abbrev shortComplex (A : AdicTowerStructure G ℓ) (n m : ℕ) : ShortComplex C :=
  ShortComplex.mk _ _ (A.ι_map n m)

/-- The morphism of short exact sequences from `(k, m)` to `(n, m)`, `n ≤ k`, given by the
transition maps and the identity of `Gₘ`. -/
def shortComplexMapOfLE (A : AdicTowerStructure G ℓ) {n k : ℕ} (m : ℕ) (h : n ≤ k) :
    A.shortComplex k m ⟶ A.shortComplex n m where
  τ₁ := G.map (homOfLE h).op
  τ₂ := G.map (homOfLE (Nat.add_le_add_right h m)).op
  τ₃ := 𝟙 _
  comm₁₂ := A.map_comp_ι m h
  comm₂₃ := by
    rw [Category.comp_id, ← G.map_comp]
    rfl

/-- The morphism of short exact sequences from `(n, m + c)` to `(n + c, m)` given by
`ιₙ꜀ : Gₙ ⟶ Gₙ₊꜀`, the identification `Gₙ₊₍ₘ₊꜀₎ = G₍ₙ₊꜀₎₊ₘ` and the transition map
`Gₘ₊꜀ ⟶ Gₘ`. -/
def shortComplexMapShift (A : AdicTowerStructure G ℓ) (n m c : ℕ) :
    A.shortComplex n (m + c) ⟶ A.shortComplex (n + c) m where
  τ₁ := A.ι n c
  τ₂ := G.map (homOfLE (by omega : n + c + m ≤ n + (m + c))).op
  τ₃ := G.map (homOfLE (Nat.le_add_right m c)).op
  comm₁₂ := by
    have := A.epi_map (Nat.le_add_right n (m + c))
    dsimp
    have e : (homOfLE (Nat.le_add_right n (m + c))).op =
        (homOfLE (by omega : n + c + m ≤ n + (m + c))).op ≫
          (homOfLE (Nat.le_add_right (n + c) m)).op ≫ (homOfLE (Nat.le_add_right n c)).op :=
      Subsingleton.elim _ _
    rw [← cancel_epi (G.map (homOfLE (Nat.le_add_right n (m + c))).op),
      reassoc_of% (A.map_ι n (m + c)), e, G.map_comp, G.map_comp, Category.assoc,
      Category.assoc, reassoc_of% (A.map_ι n c)]
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id, A.map_ι]
    rw [smul_smul, ← pow_add, add_comm c m]
  comm₂₃ := by
    dsimp
    rw [← G.map_comp, ← G.map_comp]
    rfl


/-- In an abelian category, if `f = p ≫ i` with `p` an epimorphism and `kernel.ι f ≫ p = 0`,
then `i` is a monomorphism. -/
lemma _root_.CategoryTheory.Abelian.mono_of_epi_of_kernel_ι_comp_eq_zero {X Y Z : C}
    {f : X ⟶ Z} {p : X ⟶ Y} {i : Y ⟶ Z} [Epi p] (hf : p ≫ i = f) (hk : kernel.ι f ≫ p = 0) :
    Mono i := by
  refine Preadditive.mono_of_cancel_zero _ fun {P} g hg ↦ ?_
  have h₁ : pullback.fst p g ≫ f = 0 := by
    rw [← hf, ← Category.assoc, pullback.condition, Category.assoc, hg, Limits.comp_zero]
  have h₂ : pullback.snd p g ≫ g = 0 := by
    rw [← pullback.condition, ← kernel.lift_ι f _ h₁, Category.assoc, hk, Limits.comp_zero]
  exact zero_of_epi_comp _ h₂

lemma pow_smul_id_comp_map_eq_zero (G : ℕᵒᵖ ⥤ C) (ℓ : ℕ)
    (hzero : ∀ n : ℕ, ℓ ^ n • 𝟙 (G.obj (op n)) = 0) {n k : ℕ} (h : n ≤ k) :
    (ℓ ^ n • 𝟙 (G.obj (op k))) ≫ G.map (homOfLE h).op = 0 := by
  rw [Linear.smul_comp, Category.id_comp, ← Category.comp_id (G.map (homOfLE h).op),
    ← Linear.comp_smul, hzero, Limits.comp_zero]

lemma pow_smul_id_comp_pow_smul_id_eq_zero (G : ℕᵒᵖ ⥤ C) (ℓ : ℕ)
    (hzero : ∀ n : ℕ, ℓ ^ n • 𝟙 (G.obj (op n)) = 0) (n m : ℕ) :
    (ℓ ^ n • 𝟙 (G.obj (op (n + m)))) ≫ (ℓ ^ m • 𝟙 (G.obj (op (n + m)))) = 0 := by
  rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul, ← pow_add, hzero]

/-- **`ℓ`-adic tower structures from flat towers.** Let `(Gₙ)` be a tower with `ℓⁿ Gₙ = 0` whose
transition maps `G_k ⟶ Gₙ` are cokernels of `ℓⁿ : G_k ⟶ G_k`, and which is flat:
`G_{n+m} --ℓⁿ--> G_{n+m} --ℓᵐ--> G_{n+m}` is exact. Then the maps `ιₙₘ : Gₙ ⟶ Gₙ₊ₘ` induced by
`ℓᵐ : Gₙ₊ₘ ⟶ Gₙ₊ₘ` form an `ℓ`-adic tower structure. -/
noncomputable def ofIsColimit (G : ℕᵒᵖ ⥤ C) (ℓ : ℕ)
    (hzero : ∀ n : ℕ, ℓ ^ n • 𝟙 (G.obj (op n)) = 0)
    (hcoker : ∀ {n k : ℕ} (h : n ≤ k), IsColimit (CokernelCofork.ofπ (G.map (homOfLE h).op)
      (pow_smul_id_comp_map_eq_zero G ℓ hzero h)))
    (hflat : ∀ n m : ℕ, (ShortComplex.mk _ _
      (pow_smul_id_comp_pow_smul_id_eq_zero G ℓ hzero n m)).Exact) :
    AdicTowerStructure G ℓ :=
  have hι (n m : ℕ) := CokernelCofork.IsColimit.desc' (hcoker (Nat.le_add_right n m))
    (ℓ ^ m • 𝟙 (G.obj (op (n + m)))) (pow_smul_id_comp_pow_smul_id_eq_zero G ℓ hzero n m)
  have hι' (n m : ℕ) : G.map (homOfLE (Nat.le_add_right n m)).op ≫ (hι n m).1 =
      ℓ ^ m • 𝟙 (G.obj (op (n + m))) := (hι n m).2
  have hepi {n k : ℕ} (h : n ≤ k) : Epi (G.map (homOfLE h).op) :=
    epi_of_isColimit_cofork (hcoker h)
  have ι_map (n m : ℕ) : (hι n m).1 ≫ G.map (homOfLE (Nat.le_add_left m n)).op = 0 := by
    have := hepi (Nat.le_add_right n m)
    rw [← cancel_epi (G.map (homOfLE (Nat.le_add_right n m)).op), reassoc_of% (hι' n m),
      Limits.comp_zero, pow_smul_id_comp_map_eq_zero G ℓ hzero (Nat.le_add_left m n)]
  { ι n m := (hι n m).1
    map_ι := hι'
    ι_map
    shortExact n m := by
      have := hepi (Nat.le_add_right n m)
      have := hepi (Nat.le_add_left m n)
      have hS : (ShortComplex.mk _ _ (pow_smul_id_comp_map_eq_zero G ℓ hzero
          (Nat.le_add_left m n))).Exact :=
        ShortComplex.exact_of_g_is_cokernel _ (hcoker (Nat.le_add_left m n))
      let φ : ShortComplex.mk _ _ (pow_smul_id_comp_map_eq_zero G ℓ hzero
          (Nat.le_add_left m n)) ⟶ ShortComplex.mk _ _ (ι_map n m) :=
        { τ₁ := G.map (homOfLE (Nat.le_add_right n m)).op
          τ₂ := 𝟙 _
          τ₃ := 𝟙 _
          comm₁₂ := by
            dsimp
            rw [Category.comp_id, hι' n m]
          comm₂₃ := by
            dsimp
            rw [Category.id_comp, Category.comp_id] }
      have : Mono (hι n m).1 := by
        refine Abelian.mono_of_epi_of_kernel_ι_comp_eq_zero (hι' n m) ?_
        have := (ShortComplex.exact_iff_epi_kernel_lift _).1 (hflat n m)
        rw [← cancel_epi (kernel.lift (ℓ ^ m • 𝟙 (G.obj (op (n + m))))
          (ℓ ^ n • 𝟙 (G.obj (op (n + m)))) (pow_smul_id_comp_pow_smul_id_eq_zero G ℓ hzero n m)),
          kernel.lift_ι_assoc, Limits.comp_zero]
        exact pow_smul_id_comp_map_eq_zero G ℓ hzero _
      exact { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hS } }

end AdicTowerStructure

end CategoryTheory
