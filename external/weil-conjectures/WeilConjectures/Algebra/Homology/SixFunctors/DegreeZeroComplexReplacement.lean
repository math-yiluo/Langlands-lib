/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone

/-!
# Replacement of complexes by objects of degree zero

Source: Stacks Project, Derived Categories, Tag 07K6, `lemma-replace-resolution`,
the uniformly bounded finite-degree specialization
(blueprint: lem-sf-degree-zero-complex-replacement).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CochainComplex

private theorem degree_zero_object
    {C : Type u} [Category.{v} C] [Abelian C] (d : C → ℕ)
    (hembed : ∀ A : C, ∃ (I : C) (j : A ⟶ I), Mono j ∧ d I = 0)
    (hshort : ∀ S : ShortComplex C, S.ShortExact →
      d S.X₃ ≤ max (d S.X₁ - 1) (d S.X₂)) : d (0 : C) = 0 := by
  obtain ⟨I, _, _, hI⟩ := hembed 0
  let S := ShortComplex.mk (𝟙 I) (0 : I ⟶ 0) (by simp)
  have hS : S.ShortExact :=
    { exact := (S.exact_iff_epi rfl).2 inferInstance }
  have h := hshort S hS
  simpa [S, hI] using h

private theorem degree_iso
    {C : Type u} [Category.{v} C] [Abelian C] (d : C → ℕ)
    (hzero : d (0 : C) = 0)
    (hshort : ∀ S : ShortComplex C, S.ShortExact →
      d S.X₃ ≤ max (d S.X₁ - 1) (d S.X₂))
    {A B : C} (e : A ≅ B) : d A = d B := by
  have le_of_iso {A B : C} (e : A ≅ B) : d B ≤ d A := by
    let S := ShortComplex.mk (0 : (0 : C) ⟶ A) e.hom (by simp)
    have hS : S.ShortExact :=
      { exact := (S.exact_iff_mono rfl).2 inferInstance }
    simpa [S, hzero] using hshort S hS
  exact Nat.le_antisymm (le_of_iso e.symm) (le_of_iso e)

private theorem exists_mono_complex_degree_zero
    {C : Type u} [Category.{v} C] [Abelian C] (d : C → ℕ)
    (hembed : ∀ A : C, ∃ (I : C) (j : A ⟶ I), Mono j ∧ d I = 0)
    (hsum : ∀ A B : C, d (biprod A B) ≤ max (d A) (d B))
    (K : CochainComplex C ℤ) :
    ∃ (I : CochainComplex C ℤ) (j : K ⟶ I),
      (∀ n : ℤ, Mono (j.f n)) ∧ ∀ n : ℤ, d (I.X n) = 0 := by
  classical
  choose E e he hE using fun n : ℤ ↦ hembed (K.X n)
  let I : CochainComplex C ℤ := CochainComplex.of
    (fun n ↦ biprod (E n) (E (n + 1)))
    (fun n ↦ biprod.snd ≫ biprod.inl)
    (fun n ↦ by simp [Category.assoc])
  let j : K ⟶ I := CochainComplex.ofHom
    (fun n ↦ biprod.lift (e n) (K.d n (n + 1) ≫ e (n + 1))) (by
      intro n
      dsimp [I]
      simp only [CochainComplex.of_d]
      apply biprod.hom_ext <;> simp [Category.assoc])
  refine ⟨I, j, ?_, ?_⟩
  · intro n
    have : Mono (e n) := he n
    exact mono_of_mono_fac (show j.f n ≫ biprod.fst = e n by simp [j])
  · intro n
    apply Nat.eq_zero_of_le_zero
    simpa [I, hE] using hsum (E n) (E (n + 1))

private theorem exists_quasiIso_degree_pred
    {C : Type u} [Category.{v} C] [Abelian C] (d : C → ℕ)
    (hzero : d (0 : C) = 0)
    (hembed : ∀ A : C, ∃ (I : C) (j : A ⟶ I), Mono j ∧ d I = 0)
    (hsum : ∀ A B : C, d (biprod A B) ≤ max (d A) (d B))
    (hshort : ∀ S : ShortComplex C, S.ShortExact →
      d S.X₃ ≤ max (d S.X₁ - 1) (d S.X₂))
    (N : ℕ) (K : CochainComplex C ℤ) (hK : ∀ n : ℤ, d (K.X n) ≤ N + 1) :
    ∃ (L : CochainComplex C ℤ) (f : K ⟶ L),
      QuasiIso f ∧ ∀ n : ℤ, d (L.X n) ≤ N := by
  let _ := HasDerivedCategory.standard C
  obtain ⟨I, j, hmono, hI⟩ := exists_mono_complex_degree_zero d hembed hsum K
  have : Mono j := HomologicalComplex.mono_of_mono_f j hmono
  let S := ShortComplex.cokernelSequence j
  have : Mono S.f := by
    change Mono j
    infer_instance
  have hS : S.ShortExact := { exact := ShortComplex.cokernelSequence_exact j }
  let Q := cokernel j
  let p : I ⟶ Q := cokernel.π j
  have hp (n : ℤ) : Epi (p.f n) :=
    (hS.map (HomologicalComplex.eval C (.up ℤ) n)).epi_g
  have hQ (n : ℤ) : d (Q.X n) ≤ N := by
    have h := hshort (S.map (HomologicalComplex.eval C (.up ℤ) n))
      (hS.map (HomologicalComplex.eval C (.up ℤ) n))
    change d (Q.X n) ≤ max (d (K.X n) - 1) (d (I.X n)) at h
    rw [hI n, max_eq_left (Nat.zero_le _)] at h
    exact h.trans (by have := hK n; omega)
  let e : K ≅ kernel p :=
    IsLimit.conePointUniqueUpToIso hS.fIsKernel (limit.isLimit _)
  obtain ⟨κ, _, hκ, _⟩ := exists_kernel_to_shifted_mappingCone_of_degreewise_epi p hp
  have : QuasiIso κ := hκ
  refine ⟨(mappingCone p)⟦(-1 : ℤ)⟧, e.hom ≫ κ, inferInstance, ?_⟩
  intro n
  let eX := ((mappingCone p).shiftFunctorObjXIso (-1) n (n - 1) (by omega)) ≪≫
    HomologicalComplex.homotopyCofiber.XIsoBiprod p (n - 1) n (by
      change n - 1 + 1 = n
      omega)
  calc
    d (((mappingCone p)⟦(-1 : ℤ)⟧).X n) =
        d (biprod (I.X n) (Q.X (n - 1))) := degree_iso d hzero hshort eX
    _ ≤ max (d (I.X n)) (d (Q.X (n - 1))) := hsum _ _
    _ ≤ N := max_le (by rw [hI n]; exact Nat.zero_le _) (hQ (n - 1))

private theorem exists_quasiIso_degree_zero_of_term_bound
    {C : Type u} [Category.{v} C] [Abelian C] (d : C → ℕ)
    (hzero : d (0 : C) = 0)
    (hembed : ∀ A : C, ∃ (I : C) (j : A ⟶ I), Mono j ∧ d I = 0)
    (hsum : ∀ A B : C, d (biprod A B) ≤ max (d A) (d B))
    (hshort : ∀ S : ShortComplex C, S.ShortExact →
      d S.X₃ ≤ max (d S.X₁ - 1) (d S.X₂))
    (N : ℕ) (K : CochainComplex C ℤ) (hK : ∀ n : ℤ, d (K.X n) ≤ N) :
    ∃ (L : CochainComplex C ℤ) (f : K ⟶ L),
      QuasiIso f ∧ ∀ n : ℤ, d (L.X n) = 0 := by
  induction N generalizing K with
  | zero =>
    exact ⟨K, 𝟙 K, inferInstance, fun n ↦ Nat.eq_zero_of_le_zero (hK n)⟩
  | succ N ih =>
    obtain ⟨M, f, hf, hM⟩ := exists_quasiIso_degree_pred d hzero hembed hsum hshort N K hK
    obtain ⟨L, g, hg, hL⟩ := ih M hM
    have : QuasiIso f := hf
    have : QuasiIso g := hg
    exact ⟨L, f ≫ g, inferInstance, hL⟩

/-- A uniformly bounded nonnegative degree function admitting embeddings into degree-zero
objects, bounded on binary direct sums by the maximum, and decreasing on cokernels as
specified below admits a degree-zero replacement of every integer-indexed cochain complex.

Source: Stacks Project, Derived Categories, Tag 07K6, `lemma-replace-resolution`
(blueprint: lem-sf-degree-zero-complex-replacement).

Proof (finite induction for the uniformly bounded specialization):
1. Embed zero in an object E of degree zero. The inequality for E → E → 0 gives
   d(0) = 0. Applying the inequality to 0 → A → B for an isomorphism and its inverse
   shows that d is invariant under isomorphisms.
2. Choose embeddings eⁿ : Kⁿ → Eⁿ with d(Eⁿ) = 0. Define Iⁿ = Eⁿ ⊕ Eⁿ⁺¹ and
   d_I(a, b) = (b, 0). Its differential squares to zero. The components
   jⁿ = (eⁿ, d_Kⁿ ≫ eⁿ⁺¹) define a chain map K → I, since d_K² = 0.
   Projection onto the first summand proves jⁿ mono. The direct-sum inequality
   gives d(Iⁿ) = 0. This construction uses only binary sums, even for unbounded K.
3. If every d(Kⁿ) ≤ N + 1, take the cokernel p : I → Q of j in the abelian
   category of complexes. Evaluating its short exact sequence in each degree gives
   d(Qⁿ) ≤ max(d(Kⁿ) - 1, d(Iⁿ)) ≤ N. The map p is degreewise epic, and the
   kernel universal property gives an isomorphism K ≅ ker(p).
4. Apply `lem-weil-degreewise-epi-kernel-cocone-qis` to p. It gives a quasi-isomorphism
   ker(p) → Cone(p)[-1], hence one from K. The term in degree n of the shifted cone
   is isomorphic to Iⁿ ⊕ Qⁿ⁻¹. Isomorphism invariance and the direct-sum inequality
   bound its degree by N. Thus a finite cone construction lowers the term bound by one.
5. Induct on the bound. At zero take the identity. At N + 1 apply step 4, then the
   induction hypothesis at N, and compose the quasi-isomorphisms. Finally apply the
   termwise result with the given global bound D.

The explicit finite argument is written by V2 using the kernel/cone comparison of
Stacks Tags 070M and 014Q; the statement is the uniformly bounded case of Tag 07K6.
-/
theorem exists_quasiIso_degree_zero_of_bounded_degree
    (C : Type u) [Category.{v} C] [Abelian C]
    (d : C → ℕ) (D : ℕ) (hbound : ∀ A : C, d A ≤ D)
    (hembed : ∀ A : C, ∃ (I : C) (j : A ⟶ I), Mono j ∧ d I = 0)
    (hsum : ∀ A B : C, d (biprod A B) ≤ max (d A) (d B))
    (hshort : ∀ S : ShortComplex C, S.ShortExact →
      d S.X₃ ≤ max (d S.X₁ - 1) (d S.X₂))
    (K : CochainComplex C ℤ) :
    ∃ (L : CochainComplex C ℤ) (f : K ⟶ L),
      QuasiIso f ∧ ∀ r : ℤ, d (L.X r) = 0 := by
  exact exists_quasiIso_degree_zero_of_term_bound d
    (degree_zero_object d hembed hshort) hembed hsum hshort D K (fun n ↦ hbound (K.X n))

end CochainComplex
