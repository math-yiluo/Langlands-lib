/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-! # Contractibility of the power-set complex
Source: literature/stacks-project/sites-cohomology.tex, Tag 03AT
(blueprint: lem-weil-pbc-power-set-complex-contractible)
-/

@[expose] public section

open scoped BigOperators

namespace Algebra

universe u v

variable (A : Type u) [Ring A] (S : Type v)

/-- The free `A`-module on `(p+1)`-tuples in `S`.
Source: Stacks Project, Tag 03AT (blueprint: lem-weil-pbc-power-set-complex-contractible). -/
abbrev powerSetComplexObject (p : ℕ) : Type (max u v) := (Fin (p + 1) → S) →₀ A

/-- Deletion of the `j`-th entry of a tuple.
Source: Stacks Project, Tag 03AT (blueprint: lem-weil-pbc-power-set-complex-contractible). -/
def powerSetComplexFace {p : ℕ} (j : Fin (p + 2))
    (x : Fin (p + 2) → S) : Fin (p + 1) → S :=
  fun i => x (Fin.succAbove j i)

/-- The alternating face differential on free modules on tuples.
Source: Stacks Project, Tag 03AT (blueprint: lem-weil-pbc-power-set-complex-contractible). -/
noncomputable def powerSetComplexDifferential (p : ℕ) :
    powerSetComplexObject A S (p + 1) →ₗ[A] powerSetComplexObject A S p :=
  (Finsupp.lift _ _ _) (fun x =>
    ∑ j : Fin (p + 2),
      ((-1 : A) ^ (j : ℕ)) • Finsupp.single (powerSetComplexFace S (p := p) j x) 1)

/-- The augmentation sending each basis element to `1`.
Source: Stacks Project, Tag 03AT (blueprint: lem-weil-pbc-power-set-complex-contractible). -/
noncomputable def powerSetComplexAugmentation :
    powerSetComplexObject A S 0 →ₗ[A] A :=
  (Finsupp.lift _ _ _) (fun _ => 1)

/-- The contracting homotopy `[(s₀,…,sₚ)] ↦ [(s,s₀,…,sₚ)]` prefixing a chosen `s : S`.
Source: Stacks Project, Tag 03AT (blueprint: lem-weil-pbc-power-set-complex-contractible). -/
noncomputable def powerSetComplexHomotopy (s : S) (p : ℕ) :
    powerSetComplexObject A S p →ₗ[A] powerSetComplexObject A S (p + 1) :=
  Finsupp.lmapDomain A A (fun x : Fin (p + 1) → S => (Fin.cons s x : Fin (p + 2) → S))

/-- The degree `-1` part of the contracting homotopy, `A → C₀(S;A)`, `1 ↦ [s]`.
Source: Stacks Project, Tag 03AT (blueprint: lem-weil-pbc-power-set-complex-contractible). -/
noncomputable def powerSetComplexAugmentationHomotopy (s : S) :
    A →ₗ[A] powerSetComplexObject A S 0 :=
  Finsupp.lsingle (fun _ => s)


private theorem powerSetComplexFace_cons_zero (p : ℕ) (s : S)
    (x : Fin (p + 1) → S) :
    powerSetComplexFace S (p := p) 0 (Fin.cons s x) = x := by
  funext i
  simp [powerSetComplexFace]

private theorem powerSetComplexFace_cons_succ (p : ℕ) (s : S)
    (x : Fin (p + 2) → S) (j : Fin (p + 2)) :
    powerSetComplexFace S (p := p + 1) j.succ (Fin.cons s x) =
      Fin.cons s (powerSetComplexFace S j x) := by
  exact Fin.cons_comp_succ_succAbove s x j

/-- Contracting homotopy identities on basis tuples.
Source: Stacks Project, Tag 03AT.
Proof: evaluate the maps on each basis tuple; the first face is the identity and
the remaining alternating faces are the prefix of the differential.
(blueprint: lem-weil-pbc-power-set-complex-homotopy-identities) -/
theorem powerSetComplex_homotopy_identities :
    ∀ s : S,
      (powerSetComplexAugmentation A S).comp
          (powerSetComplexAugmentationHomotopy A S s) = LinearMap.id ∧
      (powerSetComplexDifferential A S 0).comp (powerSetComplexHomotopy A S s 0) +
          (powerSetComplexAugmentationHomotopy A S s).comp
            (powerSetComplexAugmentation A S) = LinearMap.id ∧
      ∀ p : ℕ,
        (powerSetComplexDifferential A S (p + 1)).comp
            (powerSetComplexHomotopy A S s (p + 1)) +
          (powerSetComplexHomotopy A S s p).comp
            (powerSetComplexDifferential A S p) = LinearMap.id := by
  intro s
  refine ⟨?_, ?_, ?_⟩
  · apply LinearMap.ext_ring
    simp [powerSetComplexAugmentation, powerSetComplexAugmentationHomotopy]
  · apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    have hf : powerSetComplexFace S (p := 0) 1 (Fin.cons s x) = (fun _ => s) := by
      funext i
      fin_cases i
      rfl
    simp [powerSetComplexDifferential, powerSetComplexHomotopy,
      powerSetComplexAugmentation, powerSetComplexAugmentationHomotopy,
      Fin.sum_univ_succ, powerSetComplexFace_cons_zero, hf]
  · intro p
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, LinearMap.add_apply, Finsupp.lsingle_apply,
      LinearMap.id_apply]
    simp only [powerSetComplexHomotopy, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single]
    simp only [powerSetComplexDifferential, Finsupp.lift_apply,
      Finsupp.sum_single_index, zero_smul, one_smul]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, powerSetComplexFace_cons_zero,
      powerSetComplexFace_cons_succ, Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
    simp only [Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_smul, Finsupp.mapDomain_single]
    rw [Finset.sum_neg_distrib]
    simp

/-- Basis computation of d²=0, εd=0, and the empty case.
Source: Stacks Project, Tag 03AT.
Proof: compute both compositions on Finsupp basis elements and use sign cancellation;
when S is empty every tuple type is empty.
(blueprint: lem-weil-pbc-power-set-complex-basic-identities) -/
theorem powerSetComplex_basic_identities :
    (∀ p : ℕ,
      (powerSetComplexDifferential A S p).comp
          (powerSetComplexDifferential A S (p + 1)) = 0) ∧
    (powerSetComplexAugmentation A S).comp
          (powerSetComplexDifferential A S 0) = 0 ∧
    (IsEmpty S → ∀ p : ℕ, Subsingleton (powerSetComplexObject A S p)) := by
  have hed : (powerSetComplexAugmentation A S).comp
      (powerSetComplexDifferential A S 0) = 0 := by
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply,
      powerSetComplexDifferential, Finsupp.lift_apply, Finsupp.sum_single_index,
      zero_smul, one_smul]
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero, pow_one,
      one_smul, neg_smul, zero_add, map_add, map_neg]
    simp [powerSetComplexAugmentation]
  refine ⟨?_, hed, ?_⟩
  · intro p
    induction p with
    | zero =>
      apply Finsupp.lhom_ext'
      intro x
      apply LinearMap.ext_ring
      let s := x 0
      let y := Fin.tail x
      have hx : powerSetComplexHomotopy A S s 1 (Finsupp.single y 1) =
          Finsupp.single x 1 := by
        simp [powerSetComplexHomotopy, s, y]
      rcases powerSetComplex_homotopy_identities A S s with ⟨_, hzero, hsucc⟩
      have h1 := congrArg (powerSetComplexDifferential A S 0)
        (LinearMap.congr_fun (hsucc 0) (Finsupp.single y 1))
      have h2 := LinearMap.congr_fun hzero
        (powerSetComplexDifferential A S 0 (Finsupp.single y 1))
      have he := LinearMap.congr_fun hed (Finsupp.single y 1)
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
        LinearMap.zero_apply] at h1 h2 he
      rw [he, map_zero, add_zero] at h2
      rw [map_add, hx, h2] at h1
      simpa using (add_eq_right.mp h1)
    | succ p ih =>
      apply Finsupp.lhom_ext'
      intro x
      apply LinearMap.ext_ring
      let s := x 0
      let y := Fin.tail x
      have hx : powerSetComplexHomotopy A S s (p + 2) (Finsupp.single y 1) =
          Finsupp.single x 1 := by
        simp [powerSetComplexHomotopy, s, y]
      rcases powerSetComplex_homotopy_identities A S s with ⟨_, _, hsucc⟩
      have h1 := congrArg (powerSetComplexDifferential A S (p + 1))
        (LinearMap.congr_fun (hsucc (p + 1)) (Finsupp.single y 1))
      have h2 := LinearMap.congr_fun (hsucc p)
        (powerSetComplexDifferential A S (p + 1) (Finsupp.single y 1))
      have he := LinearMap.congr_fun ih (Finsupp.single y 1)
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
        LinearMap.zero_apply] at h1 h2 he
      rw [he, map_zero, add_zero] at h2
      rw [map_add, hx, h2] at h1
      simpa using (add_eq_right.mp h1)
  · intro h p
    have : IsEmpty S := h
    have : IsEmpty (Fin (p + 1) → S) := ⟨fun x => isEmptyElim (x 0)⟩
    infer_instance

/-- Exactness from the chosen contracting homotopy.
Source: Stacks Project, Tag 03AT.
Proof: for a chosen element of S, prefixing gives a contracting homotopy; the
standard contracting-homotopy argument identifies each range with the next kernel.
(blueprint: lem-weil-pbc-power-set-complex-nonempty-contracting) -/
theorem powerSetComplex_nonempty_contracting :
    Nonempty S →
      (∀ p : ℕ,
        LinearMap.range (powerSetComplexDifferential A S (p + 1)) =
          LinearMap.ker (powerSetComplexDifferential A S p)) ∧
      LinearMap.range (powerSetComplexDifferential A S 0) =
        LinearMap.ker (powerSetComplexAugmentation A S) ∧
      LinearMap.range (powerSetComplexAugmentation A S) = ⊤ := by
  rintro ⟨s⟩
  rcases powerSetComplex_basic_identities A S with ⟨hdd, hed, _⟩
  rcases powerSetComplex_homotopy_identities A S s with ⟨heh, hzero, hsucc⟩
  refine ⟨?_, ?_, ?_⟩
  · intro p
    apply le_antisymm
    · exact LinearMap.range_le_ker_iff.mpr (hdd p)
    · intro x hx
      have hx0 := LinearMap.mem_ker.mp hx
      refine LinearMap.mem_range.mpr ⟨powerSetComplexHomotopy A S s (p + 1) x, ?_⟩
      have h := LinearMap.congr_fun (hsucc p) x
      simpa [hx0] using h
  · apply le_antisymm
    · exact LinearMap.range_le_ker_iff.mpr hed
    · intro x hx
      have hx0 := LinearMap.mem_ker.mp hx
      refine LinearMap.mem_range.mpr ⟨powerSetComplexHomotopy A S s 0 x, ?_⟩
      have h := LinearMap.congr_fun hzero x
      simpa [hx0] using h
  · apply LinearMap.range_eq_top.mpr
    intro x
    refine ⟨powerSetComplexAugmentationHomotopy A S s x, ?_⟩
    exact LinearMap.congr_fun heh x

/-- The tuple complex `C_•(S;A)` with `d ∘ d = 0` and `ε ∘ d = 0`; it is zero when `S` is
empty; for nonempty `S` the augmented complex `⋯ → C₁ → C₀ → A → 0` is exact in every
degree (at `C_{p+1}`, at `C₀`, and at `A`: `ε` is surjective), so `H_p = 0` for `p > 0` and
`ε` induces `H₀ ≅ A`; and for every `s : S` the prefixing maps form a contracting homotopy of
the augmented complex.
Source: Stacks Project, Lemma Tag 03AT, last paragraph of the proof
(blueprint: lem-weil-pbc-power-set-complex-contractible).
Proof: (1) `d ∘ d = 0` and `ε ∘ d = 0` on basis tuples by the sign cancellation of the
two deletion orders, and `ε(d[(s₀,s₁)]) = 1 - 1 = 0`. (2) If `S` is empty there are no
tuples, so every `C_p` is zero. (3) For `s : S`, on basis elements
`d(h x) = x - h(d x)` in positive degrees, `d(h[s₀]) + h(ε[s₀]) = [s₀]` and `ε(h 1) = 1`.
(4) A contracting homotopy of the augmented complex gives its exactness in every degree
(lem-weil-pbc-contractible-complex-acyclic). -/
theorem powerSetComplex_contractible :
    (∀ p : ℕ,
      (powerSetComplexDifferential A S p).comp
          (powerSetComplexDifferential A S (p + 1)) = 0) ∧
    (powerSetComplexAugmentation A S).comp
          (powerSetComplexDifferential A S 0) = 0 ∧
    (IsEmpty S → ∀ p : ℕ, Subsingleton (powerSetComplexObject A S p)) ∧
    (Nonempty S →
      (∀ p : ℕ,
        LinearMap.range (powerSetComplexDifferential A S (p + 1)) =
          LinearMap.ker (powerSetComplexDifferential A S p)) ∧
      LinearMap.range (powerSetComplexDifferential A S 0) =
        LinearMap.ker (powerSetComplexAugmentation A S) ∧
      LinearMap.range (powerSetComplexAugmentation A S) = ⊤) ∧
    (∀ s : S,
      (powerSetComplexAugmentation A S).comp
          (powerSetComplexAugmentationHomotopy A S s) = LinearMap.id ∧
      (powerSetComplexDifferential A S 0).comp (powerSetComplexHomotopy A S s 0) +
          (powerSetComplexAugmentationHomotopy A S s).comp
            (powerSetComplexAugmentation A S) = LinearMap.id ∧
      ∀ p : ℕ,
        (powerSetComplexDifferential A S (p + 1)).comp
            (powerSetComplexHomotopy A S s (p + 1)) +
          (powerSetComplexHomotopy A S s p).comp
            (powerSetComplexDifferential A S p) = LinearMap.id) := by
  rcases powerSetComplex_basic_identities A S with ⟨hdd, hed, hempty⟩
  refine ⟨hdd, hed, hempty, ?_, ?_⟩
  · exact powerSetComplex_nonempty_contracting A S
  · exact powerSetComplex_homotopy_identities A S

end Algebra
