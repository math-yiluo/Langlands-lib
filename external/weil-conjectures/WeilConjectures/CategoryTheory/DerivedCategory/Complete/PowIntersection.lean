/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.RingTheory.Filtration
public import WeilConjectures.Algebra.Category.ModuleCat.IhomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

/-!
# Infinitely divisible morphisms between perfect complexes vanish

Let `R` be a Noetherian local ring and `x` an element of its maximal ideal. By Krull's
intersection theorem, a finitely generated `R`-module contains no nonzero element which is
divisible by every power of `x`. We apply this to the `R`-modules of morphisms in the derived
category `D(R)`, which are finitely generated between perfect complexes.

## Main statements

- `IsLocalRing.eq_zero_of_forall_eq_pow_smul`: in a finitely generated module over a Noetherian
  local ring, an element divisible by all powers of `x ∈ 𝔪` vanishes.
- `DerivedCategory.eq_zero_of_forall_eq_pow_smul`: the same for a morphism `f : A ⟶ B` in `D(R)`
  when `A ⟶ B` is a finitely generated `R`-module.
- `DerivedCategory.IsPerfect.finite_hom`: over a Noetherian ring, the `R`-module of morphisms
  between perfect complexes is finitely generated.
- `DerivedCategory.IsPerfect.eq_zero_of_forall_eq_pow_smul`: over a Noetherian local ring, a
  morphism between perfect complexes which is divisible by every power of `x ∈ 𝔪` vanishes.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace IsLocalRing

/-- **Krull's intersection theorem** for elements: in a finitely generated module over a
Noetherian local ring, an element which is divisible by every power of an element `x` of the
maximal ideal is zero. -/
theorem eq_zero_of_forall_eq_pow_smul {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] {x : R}
    (hx : x ∈ maximalIdeal R) {m : M} (h : ∀ n : ℕ, ∃ y : M, m = x ^ n • y) : m = 0 := by
  have hI : Ideal.span {x} ≠ ⊤ := Ideal.span_singleton_ne_top ((mem_maximalIdeal x).1 hx)
  rw [← Submodule.mem_bot R, ← Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ hI, Submodule.mem_iInf]
  intro n
  obtain ⟨y, rfl⟩ := h n
  rw [Ideal.span_singleton_pow]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

end IsLocalRing

namespace CochainComplex

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Over a Noetherian ring, morphisms from a bounded complex of finitely generated modules to a
complex of finitely generated modules form a finitely generated module: they embed into the
finite product of the modules of linear maps in the degrees where the source is nonzero. -/
theorem finite_hom {P P' : CochainComplex (ModuleCat.{v} R) ℤ} (a b : ℤ) [P.IsStrictlyGE a]
    [P.IsStrictlyLE b] (hP : ∀ i, Module.Finite R (P.X i))
    (hP' : ∀ i, Module.Finite R (P'.X i)) : Module.Finite R (P ⟶ P') := by
  have (i : Finset.Icc a b) : Module.Finite R (P.X i →ₗ[R] P'.X i) := by
    have := hP i
    have := hP' i
    exact Module.Finite.linearMap_of_isNoetherianRing
  let φ : (P ⟶ P') →ₗ[R] ((i : Finset.Icc a b) → (P.X i →ₗ[R] P'.X i)) :=
    { toFun f i := (f.f i).hom
      map_add' f g := by
        ext
        simp
      map_smul' r f := by
        ext
        simp }
  refine Module.Finite.of_injective φ fun f g hfg ↦ ?_
  ext i : 1
  by_cases hi : i ∈ Finset.Icc a b
  · exact ModuleCat.hom_ext (congr_fun hfg ⟨i, hi⟩)
  · rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hi
    rcases hi with hi | hi
    · exact (P.isZero_of_isStrictlyGE a i hi).eq_of_src _ _
    · exact (P.isZero_of_isStrictlyLE b i hi).eq_of_src _ _

end CochainComplex

namespace DerivedCategory

section Krull

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  [HasDerivedCategory.{w} (ModuleCat.{v} R)]

/-- **Krull's intersection theorem** for morphisms in `D(R)`: if `R` is a Noetherian local ring,
`x ∈ 𝔪` and `A ⟶ B` is a finitely generated `R`-module, then a morphism `f : A ⟶ B` which is
divisible by every power of `x` is zero. -/
theorem eq_zero_of_forall_eq_pow_smul {A B : DerivedCategory (ModuleCat.{v} R)}
    [Module.Finite R (A ⟶ B)] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R) {f : A ⟶ B}
    (hf : ∀ n : ℕ, ∃ g : A ⟶ B, f = x ^ n • g) : f = 0 :=
  IsLocalRing.eq_zero_of_forall_eq_pow_smul hx hf

end Krull

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]

/-- Over a Noetherian ring, the `R`-module of morphisms between perfect complexes is finitely
generated. Representing the source by a bounded complex `P` of finitely generated projective
modules, which is K-projective, every morphism `Q(P) ⟶ Q(P')` comes from a morphism of
complexes, and these form a finitely generated module by `CochainComplex.finite_hom`. -/
theorem IsPerfect.finite_hom {A B : DerivedCategory (ModuleCat.{u} R)} (hA : A.IsPerfect)
    (hB : B.IsPerfect) : Module.Finite R (A ⟶ B) := by
  obtain ⟨P, a, b, _, _, hP, ⟨e⟩⟩ := hA
  obtain ⟨P', -, -, -, -, hP', ⟨e'⟩⟩ := hB
  have (n : ℤ) : Projective (P.X n) := by
    have := (hP n).1
    exact ModuleCat.projective_of_categoryTheory_projective _
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective _ b
  have : Module.Finite R (P ⟶ P') :=
    CochainComplex.finite_hom a b (fun i ↦ (hP i).2) fun i ↦ (hP' i).2
  have : Module.Finite R (Q.obj P ⟶ Q.obj P') :=
    Module.Finite.of_surjective (Q.mapLinearMap R) fun g ↦
      CochainComplex.IsKProjective.exists_Q_map_eq P P' g
  exact Module.Finite.equiv (Linear.homCongr R e e').symm

/-- A morphism between perfect complexes over a Noetherian local ring `R` which is divisible by
every power of an element `x` of the maximal ideal is zero. -/
theorem IsPerfect.eq_zero_of_forall_eq_pow_smul [IsLocalRing R]
    {A B : DerivedCategory (ModuleCat.{u} R)} (hA : A.IsPerfect) (hB : B.IsPerfect) {x : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) {f : A ⟶ B}
    (hf : ∀ n : ℕ, ∃ g : A ⟶ B, f = x ^ n • g) : f = 0 :=
  have := hA.finite_hom hB
  DerivedCategory.eq_zero_of_forall_eq_pow_smul hx hf

end DerivedCategory
