/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Data.Nat.Choose.Basic

/-! # Binomial sums of shifted objects

Source: Stacks Project, Tag 08EK, binomial expansion in the cone construction
(blueprint: lem-sc-binomial-shift-biproduct).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private abbrev BinomialIndex (n : ℕ) :=
  (j : Fin (n + 1)) × Fin (Nat.choose n j.val)

private def binomialIndexStep (n : ℕ) :
    BinomialIndex n ⊕ BinomialIndex n → BinomialIndex (n + 1)
  | Sum.inl ⟨j, c⟩ => ⟨j.castSucc, ⟨c.val,
      lt_of_lt_of_le c.isLt (Nat.choose_le_succ n j.val)⟩⟩
  | Sum.inr ⟨j, c⟩ => ⟨j.succ, ⟨Nat.choose n (j.val + 1) + c.val, by
      simp only [Fin.val_succ]
      rw [Nat.choose_succ_succ']
      omega⟩⟩

private theorem binomialIndexStep_injective (n : ℕ) :
    Function.Injective (binomialIndexStep n) := by
  intro x y h
  have hj := congrArg (fun p : BinomialIndex (n + 1) ↦ p.1.val) h
  have hc := congrArg (fun p : BinomialIndex (n + 1) ↦ p.2.val) h
  cases x with
  | inl x =>
    obtain ⟨j, c⟩ := x
    cases y with
    | inl y =>
      obtain ⟨k, d⟩ := y
      dsimp [binomialIndexStep] at hj hc
      have he : j = k := Fin.ext hj
      subst k
      have : c = d := Fin.ext hc
      subst d
      rfl
    | inr y =>
      obtain ⟨k, d⟩ := y
      dsimp [binomialIndexStep] at hj hc
      have := c.isLt
      simp only [hj] at this
      omega
  | inr x =>
    obtain ⟨j, c⟩ := x
    cases y with
    | inl y =>
      obtain ⟨k, d⟩ := y
      dsimp [binomialIndexStep] at hj hc
      have := d.isLt
      simp only [← hj] at this
      omega
    | inr y =>
      obtain ⟨k, d⟩ := y
      dsimp [binomialIndexStep] at hj hc
      have he : j = k := Fin.ext (by omega)
      subst k
      have : c = d := Fin.ext (by omega)
      subst d
      rfl

private theorem binomialIndexStep_surjective (n : ℕ) :
    Function.Surjective (binomialIndexStep n) := by
  intro p
  obtain ⟨j, c⟩ := p
  by_cases hc : c.val < Nat.choose n j.val
  · have hj : j.val < n + 1 := by
      by_contra h
      have hz : Nat.choose n j.val = 0 := Nat.choose_eq_zero_of_lt (by omega)
      omega
    refine ⟨Sum.inl ⟨⟨j.val, hj⟩, ⟨c.val, hc⟩⟩, ?_⟩
    refine Sigma.ext (Fin.ext rfl) ?_
    exact HEq.rfl
  · have hj : 0 < j.val := by
      by_contra h
      have hz : j.val = 0 := by omega
      have := c.isLt
      simp [hz, Nat.choose_zero_right] at hc this
      omega
    let k : Fin (n + 1) := ⟨j.val - 1, by have := j.isLt; omega⟩
    have hk : k.val + 1 = j.val := by dsimp [k]; omega
    have hchoose : Nat.choose (n + 1) j.val =
        Nat.choose n k.val + Nat.choose n j.val := by
      rw [← hk, Nat.choose_succ_succ']
    have hd : c.val - Nat.choose n j.val < Nat.choose n k.val := by
      have := c.isLt
      simp only [hchoose] at this
      omega
    refine ⟨Sum.inr ⟨k, ⟨c.val - Nat.choose n j.val, hd⟩⟩, ?_⟩
    have he : k.succ = j := Fin.ext hk
    refine Sigma.ext he ?_
    apply (Fin.heq_ext_iff (congrArg (Nat.choose (n + 1)) hk)).2
    dsimp [binomialIndexStep]
    rw [hk]
    omega

private noncomputable def sumBiproductIso {D : Type*} [Category D]
    [HasZeroMorphisms D] [HasFiniteBiproducts D] [HasBinaryBiproducts D]
    (I J : Type) [Finite I] [Finite J] (f : I → D) (g : J → D) :
    biproduct f ⊞ biproduct g ≅ biproduct (Sum.elim f g) where
  hom := biprod.desc
    (biproduct.desc fun i ↦ biproduct.ι (Sum.elim f g) (Sum.inl i))
    (biproduct.desc fun j ↦ biproduct.ι (Sum.elim f g) (Sum.inr j))
  inv := biproduct.desc (fun t ↦ match t with
    | Sum.inl i => biproduct.ι f i ≫ biprod.inl
    | Sum.inr j => biproduct.ι g j ≫ biprod.inr)
  hom_inv_id := by
    apply biprod.hom_ext'
    · apply biproduct.hom_ext'
      intro i
      simp
    · apply biproduct.hom_ext'
      intro j
      simp
  inv_hom_id := by
    apply biproduct.hom_ext'
    intro t
    cases t <;> simp

private theorem binomial_biproduct_succ (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (F : schemeDerivedCategory Y) (n : ℕ) : Nonempty
      ((biproduct (fun p : BinomialIndex n ↦ F⟦(p.1.val : ℤ)⟧)) ⊞
        (biproduct (fun p : BinomialIndex n ↦ F⟦(p.1.val : ℤ)⟧))⟦(1 : ℤ)⟧ ≅
      biproduct (fun p : BinomialIndex (n + 1) ↦ F⟦(p.1.val : ℤ)⟧)) := by
  let e := Equiv.ofBijective (binomialIndexStep n)
    ⟨binomialIndexStep_injective n, binomialIndexStep_surjective n⟩
  let f := fun p : BinomialIndex n ↦ F⟦(p.1.val : ℤ)⟧
  let g := fun p : BinomialIndex n ↦ F⟦(p.1.val : ℤ)⟧⟦(1 : ℤ)⟧
  refine ⟨biprod.mapIso (Iso.refl _) ((shiftFunctor _ (1 : ℤ)).mapBiproduct f) ≪≫
    sumBiproductIso _ _ f g ≪≫
      (biproduct.whiskerEquiv (f := Sum.elim f g)
        (g := fun p : BinomialIndex (n + 1) ↦ F⟦(p.1.val : ℤ)⟧) e ?_)⟩
  intro t
  cases t with
  | inl p => exact Iso.refl _
  | inr p =>
    change F⟦((p.1.val + 1 : ℕ) : ℤ)⟧ ≅ F⟦(p.1.val : ℤ)⟧⟦(1 : ℤ)⟧
    simpa only [Nat.cast_add, Nat.cast_one, Functor.comp_obj] using
      (shiftFunctorAdd' (schemeDerivedCategory Y) (p.1.val : ℤ) 1
        (p.1.val + 1 : ℤ) (by omega)).app F

/-- Binomial sums start with F plus F[1], and adding the shift of the nth sum
produces the (n+1)st sum.
Source: Stacks Project, Tag 08EK, cone construction and Pascal's identity
(blueprint: lem-sc-binomial-shift-biproduct).

Proof: In degree one the indexing type consists of the unique copy at j=0 and
unique copy at j=1, so the biproduct is F[0] plus F[1]; the zero shift is naturally
isomorphic to F. For the recursive identity, distribute the shift over the finite
biproduct and use F[j][1] isomorphic to F[j+1]. The unshifted summands at degree j
have multiplicity choose(n,j), and the shifted summands have multiplicity
choose(n,j-1). Concatenate these two finite lists. Pascal's identity identifies
their combined length with choose(n+1,j). At j=0 there is no shifted summand;
at j=n+1 there is no unshifted summand; both multiplicities are one. Reindexing
biproducts along these bijections gives the isomorphism. The same description
works for n=0, where the unique input summand is F. -/
theorem binomial_shift_biproduct (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (F : schemeDerivedCategory Y) :
    Nonempty (F ⊞ F⟦(1 : ℤ)⟧ ≅
      biproduct (fun p : (j : Fin 2) × Fin (Nat.choose 1 j.val) ↦ F⟦(p.1.val : ℤ)⟧)) ∧
    (∀ n : ℕ, Nonempty
      ((biproduct (fun p : (j : Fin (n + 1)) × Fin (Nat.choose n j.val) ↦
          F⟦(p.1.val : ℤ)⟧)) ⊞
        (biproduct (fun p : (j : Fin (n + 1)) × Fin (Nat.choose n j.val) ↦
          F⟦(p.1.val : ℤ)⟧))⟦(1 : ℤ)⟧ ≅
      biproduct (fun p : (j : Fin (n + 2)) × Fin (Nat.choose (n + 1) j.val) ↦
        F⟦(p.1.val : ℤ)⟧))) := by
  have hsucc := binomial_biproduct_succ Y F
  refine ⟨?_, hsucc⟩
  let : Unique (BinomialIndex 0) :=
    { default := ⟨0, ⟨0, by simp⟩⟩
      uniq := by
        rintro ⟨j, c⟩
        have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
        subst j
        congr 1
        apply Fin.ext
        have := c.isLt
        simp only [Fin.val_zero, Nat.choose_zero_right] at this ⊢
        omega }
  let e₀ : biproduct (fun p : BinomialIndex 0 ↦ F⟦(p.1.val : ℤ)⟧) ≅ F :=
    biproductUniqueIso _ ≪≫ (shiftFunctorZero _ ℤ).app F
  obtain ⟨e₁⟩ := hsucc 0
  exact ⟨biprod.mapIso e₀.symm ((shiftFunctor _ (1 : ℤ)).mapIso e₀.symm) ≪≫ e₁⟩

end AlgebraicGeometry.Scheme
