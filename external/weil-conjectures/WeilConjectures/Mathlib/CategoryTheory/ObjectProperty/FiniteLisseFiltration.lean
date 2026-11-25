/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.CategoryTheory.Simple

/-! # Finite filtrations from an additive faithful natural-number rank

Source: theorem-purity-real-sheaves-curves--1, the actual composition-filtration step, and Weil II
(1.1.6). This is the elementary categorical induction behind that step, separated from the
construction of the geometric fibre (blueprint: lem-rp-finite-lisse-filtration-of-rank).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A rank usable for the composition-filtration argument on a full class of lisse objects.
The values are natural numbers; additivity refers to ambient cokernels.
Source: theorem-purity-real-sheaves-curves--1, first and final proof paragraphs
(blueprint: lem-rp-finite-lisse-filtration-of-rank). -/
structure LisseRankData (P : ObjectProperty C) where
  rank : C → ℕ
  congr : ∀ {X Y : C}, (X ≅ Y) → rank X = rank Y
  zero : ∀ X : C, IsZero X → P X
  detects_zero : ∀ X : C, P X → rank X = 0 → IsZero X
  kernel : ∀ {X Y : C}, P X → P Y → ∀ f : X ⟶ Y, P (Limits.kernel f)
  cokernel : ∀ {X Y : C}, P X → P Y → ∀ f : X ⟶ Y, P (Limits.cokernel f)
  extension : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], P X → P (Limits.cokernel f) → P Y
  additive : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], P X → P Y →
    rank Y = rank X + rank (Limits.cokernel f)

/-- Simplicity tested only on the indicated full class of lisse objects.
Source: theorem-purity-real-sheaves-curves--1, actual composition-filtration clause
(blueprint: lem-rp-finite-lisse-filtration-of-rank). -/
def IsSimpleIn (P : ObjectProperty C) : ObjectProperty C := fun X ↦
  P X ∧ ¬ IsZero X ∧ ∀ (Y : C) (f : Y ⟶ X), P Y → Mono f → IsZero Y ∨ IsIso f

instance (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] :
    (IsSimpleIn P).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    refine ⟨P.prop_of_iso e hX.1, fun hY ↦ hX.2.1 (hY.of_iso e), ?_⟩
    intro Z f hZ hf
    let := hf
    rcases hX.2.2 Z (f ≫ e.inv) hZ inferInstance with hz | hi
    · exact Or.inl hz
    · let := hi
      right
      have heq : (f ≫ e.inv) ≫ e.hom = f := by simp
      rw [← heq]
      infer_instance

/-- An additive rank that detects zero gives a finite filtration by simple lisse quotients.
Source: theorem-purity-real-sheaves-curves--1, composition-filtration step
(blueprint: lem-rp-finite-lisse-filtration-of-rank).

Proof: induct on rank. For a nonzero object choose a proper lisse subobject of maximal
rank; its ranks form a nonempty bounded subset of the natural numbers. The quotient is
nonzero. If it had a proper nonzero lisse subobject, pull that subobject back along the
quotient map by taking the kernel of the composite quotient. Rank additivity would give
a proper lisse subobject of larger rank. Thus the quotient is simple and the chosen
subobject has smaller rank. Append this quotient to its inductive filtration.
The zero case is the empty filtration. All kernels and cokernels are ambient ones. -/
theorem filtrationClosure_isSimpleIn_of_rank
    (P : ObjectProperty C) (R : LisseRankData P) (M : C) (hM : P M) :
    (IsSimpleIn P).filtrationClosure M := by
  classical
  suffices H : ∀ r, ∀ G : C, P G → R.rank G = r →
      (IsSimpleIn P).filtrationClosure G from H _ M hM rfl
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro G hG hr
    by_cases hG0 : IsZero G
    · exact .of_isZero hG0
    let S : Set ℕ := {m | ∃ (K : C) (i : K ⟶ G), Mono i ∧ P K ∧ ¬ IsIso i ∧
      R.rank K = m}
    have hSne : S.Nonempty := by
      refine ⟨_, 0, (0 : 0 ⟶ G), inferInstance, R.zero _ (isZero_zero C), ?_, rfl⟩
      intro hi
      let := hi
      exact hG0 ((isZero_zero C).of_iso (asIso (0 : 0 ⟶ G)).symm)
    have hSb : BddAbove S := by
      refine ⟨R.rank G, ?_⟩
      rintro _ ⟨K, i, hi, hK, -, rfl⟩
      let := hi
      have := R.additive i hK hG
      omega
    obtain ⟨K, i, hi, hK, hiso, hKr⟩ := Nat.sSup_mem hSne hSb
    let := hi
    have hmax (K' : C) (i' : K' ⟶ G) (hi' : Mono i') (hK' : P K')
        (hiso' : ¬ IsIso i') : R.rank K' ≤ R.rank K :=
      hKr ▸ le_csSup hSb ⟨K', i', hi', hK', hiso', rfl⟩
    have hQ : P (cokernel i) := R.cokernel hK hG i
    have hQ0 : ¬ IsZero (cokernel i) := by
      intro h
      have : Epi i := Preadditive.epi_of_isZero_cokernel i h
      exact hiso (isIso_of_mono_of_epi i)
    have hrQ : R.rank (cokernel i) ≠ 0 := fun h ↦ hQ0 (R.detects_zero _ hQ h)
    have hadd := R.additive i hK hG
    refine .of_mono i (ih _ (by omega) K hK rfl) ⟨hQ, hQ0, ?_⟩
    intro T j hT hj
    let := hj
    by_contra! hcon
    obtain ⟨hT0, hj'⟩ := hcon
    have hQj : P (cokernel j) := R.cokernel hT hQ j
    let g := cokernel.π i ≫ cokernel.π j
    have hK' : P (kernel g) := R.kernel hG hQj g
    have hm : ¬ IsIso (kernel.ι g) := by
      intro hm
      let := hm
      have hg0 : g = 0 := by rw [← cancel_epi (kernel.ι g), kernel.condition, comp_zero]
      have hj0 : cokernel.π j = 0 := by
        rw [← cancel_epi (cokernel.π i), comp_zero]
        exact hg0
      have : Epi j := Abelian.epi_of_cokernel_π_eq_zero j hj0
      exact hj' (isIso_of_mono_of_epi j)
    have h₁ := hmax _ (kernel.ι g) inferInstance hK' hm
    let i' : K ⟶ kernel g := kernel.lift g i (by simp [g])
    have : Mono i' := mono_of_mono_fac (kernel.lift_ι g i _)
    have h₂ := R.additive i' hK hK'
    have h₃ := R.additive (kernel.ι g) hK' hG
    have h₄ := R.congr (cokernelKernelιIsoOfEpi g)
    have h₅ := R.additive j hT hQ
    exact hT0 (R.detects_zero _ hT (by omega))

/-- A concrete chain version of the rank-induction theorem, retaining lissity at every
stage. Source: theorem-purity-real-sheaves-curves--1, final composition-filtration paragraph
(blueprint: lem-rp-finite-lisse-filtration-of-rank).

Proof: extract a finite chain from filtration closure. Induct along the chain to prove
lissity of all stages, starting with the zero stage and using closure under extensions. -/
theorem exists_filtration_isSimpleIn_of_rank
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (R : LisseRankData P) (M : C) (hM : P M) :
    ∃ (n : ℕ) (G : Fin (n + 1) → C)
      (φ : ∀ i : Fin n, G i.castSucc ⟶ G i.succ),
      IsZero (G 0) ∧ Nonempty (G (Fin.last n) ≅ M) ∧ (∀ i, Mono (φ i)) ∧
      (∀ i, P (G i)) ∧ ∀ i, IsSimpleIn P (cokernel (φ i)) := by
  obtain ⟨n, G, φ, h0, hend, hmono, hsimple⟩ :=
    filtrationClosure_iff.mp (filtrationClosure_isSimpleIn_of_rank P R M hM)
  refine ⟨n, G, φ, h0, hend, hmono, ?_, hsimple⟩
  rintro ⟨i, hi⟩
  induction i with
  | zero => exact R.zero _ h0
  | succ i ih =>
    have hi' : i < n := by omega
    have := hmono ⟨i, hi'⟩
    exact R.extension (φ ⟨i, hi'⟩) (ih _) (hsimple _).1

omit [Abelian C] in
/-- Every stage of a finite monomorphism chain embeds in its terminal object.
Source: theorem-purity-real-sheaves-curves--1, actual composition filtration
(blueprint: lem-rp-finite-lisse-filtration-of-rank).

Proof: descend from the last stage, composing the next embedding with the next
monomorphism in the chain. -/
theorem exists_mono_to_endpoint_of_chain
    {n : ℕ} {G : Fin (n + 1) → C}
    (φ : ∀ i : Fin n, G i.castSucc ⟶ G i.succ) (hmono : ∀ i, Mono (φ i))
    {M : C} (e : G (Fin.last n) ≅ M) :
    ∀ i : Fin (n + 1), ∃ f : G i ⟶ M, Mono f := by
  intro i
  induction i using Fin.reverseInduction with
  | last => exact ⟨e.hom, inferInstance⟩
  | cast i ih =>
    obtain ⟨f, hf⟩ := ih
    have := hmono i
    exact ⟨φ i ≫ f, mono_comp _ _⟩

end CategoryTheory.ObjectProperty
