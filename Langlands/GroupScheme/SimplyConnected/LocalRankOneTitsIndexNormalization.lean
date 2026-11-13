import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexStatement
import Mathlib.Data.Fintype.Pi

/-! # Small Cartan diagrams in the local rank-one index enumeration -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

namespace TitsIndexData

variable {d : TitsIndexData G}

/-- Each element of the full absolute Galois group permutes the actual vertices. -/
def starPermutation (d : TitsIndexData G)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) : Equiv.Perm d.Vertex where
  toFun := d.star σ
  invFun := d.star σ⁻¹
  left_inv a := by rw [← d.star_mul, inv_mul_cancel, d.star_one]
  right_inv a := by rw [← d.star_mul, mul_inv_cancel, d.star_one]

/-- The actual full star permutation transported to a supplied numbering. -/
def numberedStar (d : TitsIndexData G) {n : ℕ} (e : d.Vertex ≃ Fin n)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) : Equiv.Perm (Fin n) :=
  e.symm.trans ((d.starPermutation σ).trans e)

@[simp] theorem numberedStar_apply {n : ℕ} (e : d.Vertex ≃ Fin n)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (i : Fin n) :
    d.numberedStar e σ i = e (d.star σ (e.symm i)) := rfl

/-- The full star action preserves every actual Cartan entry. -/
theorem cartan_star (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (a b : d.Vertex) : d.cartan (d.star σ a) (d.star σ b) = d.cartan a b :=
  (d.pinning.starAction σ).val.toHom.pairing

/-- Renumber the full matrix and the exact distinguished subset together. -/
theorem IsNumberingOf.relabel {n m : ℕ} {M : Matrix (Fin n) (Fin n) ℤ}
    {N : Matrix (Fin m) (Fin m) ℤ} {marked : Fin n → Prop}
    {marked' : Fin m → Prop} {e : d.Vertex ≃ Fin n}
    (h : d.IsNumberingOf M marked e) (q : Fin n ≃ Fin m)
    (hM : ∀ i j, M i j = N (q i) (q j))
    (hmarked : ∀ i, marked i ↔ marked' (q i)) :
    d.IsNumberingOf N marked' (e.trans q) := by
  exact ⟨fun a b => (h.1 a b).trans (hM (e a) (e b)),
    fun a => (h.2 a).trans (hmarked (e a))⟩

/-- A Cartan-automorphism classification controls each full Galois element globally. -/
theorem star_cases_of_cartan {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ}
    (e : d.Vertex ≃ Fin n) (τ : Equiv.Perm (Fin n))
    (hM : ∀ a b, d.cartan a b = M (e a) (e b))
    (hsym : ∀ f : Fin n → Fin n,
      (∀ i j, M (f i) (f j) = M i j) → (∀ i, f i = i) ∨ (∀ i, f i = τ i))
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    (∀ a, e (d.star σ a) = e a) ∨ (∀ a, e (d.star σ a) = τ (e a)) := by
  let f : Equiv.Perm (Fin n) := d.numberedStar e σ
  have hf : ∀ i j, M (f i) (f j) = M i j := by
    intro i j
    calc
      M (f i) (f j) = d.cartan (d.star σ (e.symm i)) (d.star σ (e.symm j)) :=
        (hM _ _).symm
      _ = d.cartan (e.symm i) (e.symm j) := d.cartan_star σ _ _
      _ = M i j := by simpa using hM (e.symm i) (e.symm j)
  rcases hsym f hf with hid | hτ
  · left
    intro a
    simpa [f] using hid (e a)
  · right
    intro a
    simpa [f] using hτ (e a)

/-- A rigid numbered Cartan matrix forces triviality of the full star action. -/
theorem starIsTrivial_of_cartan_rigid {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ}
    (e : d.Vertex ≃ Fin n) (hM : ∀ a b, d.cartan a b = M (e a) (e b))
    (hrigid : ∀ f : Fin n → Fin n,
      (∀ i j, M (f i) (f j) = M i j) → ∀ i, f i = i) : d.StarIsTrivial := by
  intro σ a
  apply e.injective
  have hsym : ∀ f : Fin n → Fin n,
      (∀ i j, M (f i) (f j) = M i j) →
        (∀ i, f i = i) ∨ (∀ i, f i = (1 : Equiv.Perm (Fin n)) i) :=
    fun f hf => Or.inl (hrigid f hf)
  rcases star_cases_of_cartan e 1 hM hsym σ with hid | hid
  · exact hid a
  · exact hid a

/-- Nontriviality makes a two-permutation Cartan bound an exact full-star image. -/
theorem starImagePair_of_cartan_symmetry {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℤ} (e : d.Vertex ≃ Fin n) (τ : Equiv.Perm (Fin n))
    (hM : ∀ a b, d.cartan a b = M (e a) (e b)) (hne : τ ≠ 1)
    (hsym : ∀ f : Fin n → Fin n,
      (∀ i j, M (f i) (f j) = M i j) → (∀ i, f i = i) ∨ (∀ i, f i = τ i))
    (hnot : ¬ d.StarIsTrivial) : d.StarImagePair e τ := by
  classical
  have himage := star_cases_of_cartan e τ hM hsym
  refine ⟨hne, himage, ?_⟩
  have hex : ∃ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K,
      ∃ a : d.Vertex, d.star σ a ≠ a := by
    simpa only [StarIsTrivial, not_forall] using hnot
  obtain ⟨σ, a, ha⟩ := hex
  refine ⟨σ, ?_⟩
  rcases himage σ with hid | hτ
  · exact (ha (e.injective (hid a))).elim
  · exact hτ

/-- The only Cartan symmetries of A2 and A3 are identity and chain reversal. -/
theorem starImagePair_of_small_A {n : ℕ} (hn : n = 2 ∨ n = 3)
    (e : d.Vertex ≃ Fin n)
    (hM : ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b))
    (hnot : ¬ d.StarIsTrivial) : d.StarImagePair e Fin.revPerm := by
  apply starImagePair_of_cartan_symmetry e Fin.revPerm hM _ _ hnot
  · rcases hn with rfl | rfl <;> decide
  · rcases hn with rfl | rfl <;>
      simp only [CartanMatrix.A, Matrix.of_apply] <;> decide

/-- C2 and C3 have no nonidentity Cartan symmetry, including in characteristic two. -/
theorem starIsTrivial_of_small_C {n : ℕ} (hn : n = 2 ∨ n = 3)
    (e : d.Vertex ≃ Fin n)
    (hM : ∀ a b, d.cartan a b = CartanMatrix.C n (e a) (e b)) :
    d.StarIsTrivial := by
  apply starIsTrivial_of_cartan_rigid e hM
  rcases hn with rfl | rfl <;>
    simp only [CartanMatrix.C, Matrix.of_apply] <;> decide

/-- A one-vertex absolute diagram has trivial full star action. -/
theorem starIsTrivial_of_equiv_fin_one (e : d.Vertex ≃ Fin 1) : d.StarIsTrivial := by
  intro σ a
  exact e.injective (Subsingleton.elim _ _)

/-- The fully distinguished A1 diagram is the inner-A alternative of degree one. -/
theorem hasRankOneInnerAIndex_one_of_numbering (e : d.Vertex ≃ Fin 1)
    (h : d.IsNumberingOf (CartanMatrix.A 1) (fun _ => True) e) :
    d.HasRankOneInnerAIndex 1 := by
  refine ⟨by decide, ⟨e, h.1, ?_⟩, starIsTrivial_of_equiv_fin_one e⟩
  intro a
  exact (h.2 a).trans (by
    change True ↔ (e a).val + 1 = 1
    have hi : (e a).val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (e a).isLt)
    simp only [hi, zero_add, iff_self])

/-- B1 is A1 with the same single distinguished vertex. -/
theorem hasRankOneInnerAIndex_one_of_B_one (e : d.Vertex ≃ Fin 1)
    (h : d.IsNumberingOf (CartanMatrix.B 1) (fun _ => True) e) :
    d.HasRankOneInnerAIndex 1 := by
  apply hasRankOneInnerAIndex_one_of_numbering e
  simpa only [CartanMatrix.B_one] using h

/-- C1 is A1 with the same single distinguished vertex. -/
theorem hasRankOneInnerAIndex_one_of_C_one (e : d.Vertex ≃ Fin 1)
    (h : d.IsNumberingOf (CartanMatrix.C 1) (fun _ => True) e) :
    d.HasRankOneInnerAIndex 1 := by
  apply hasRankOneInnerAIndex_one_of_numbering e
  simpa only [CartanMatrix.C_one] using h

/-- Interchanging B2's vertices sends distinguished vertex 1 to C2's vertex 2. -/
theorem hasRankOneCIndex_two_of_B_two (e : d.Vertex ≃ Fin 2)
    (h : d.IsNumberingOf (CartanMatrix.B 2) (fun i => i.val = 0) e) :
    d.HasRankOneCIndex 2 := by
  let q : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  have hq : d.IsNumberingOf (CartanMatrix.C 2) (fun i => i.val = 1) (e.trans q) :=
    h.relabel q (by
      simp only [CartanMatrix.B, CartanMatrix.C, Matrix.of_apply]
      decide) (by decide)
  exact ⟨Or.inl rfl, ⟨e.trans q, hq⟩,
    starIsTrivial_of_small_C (Or.inl rfl) (e.trans q) hq.1⟩

/-- The central distinguished vertex of inner D3 becomes the middle vertex of A3. -/
theorem hasRankOneInnerAIndex_two_of_D_three (e : d.Vertex ≃ Fin 3)
    (h : d.IsNumberingOf (CartanMatrix.D 3) (fun i => i.val = 0) e)
    (hstar : d.StarIsTrivial) : d.HasRankOneInnerAIndex 2 := by
  let q : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  have hq : d.IsNumberingOf (CartanMatrix.A 3) (fun i => i.val + 1 = 2)
      (e.trans q) := h.relabel q (by
      simp only [CartanMatrix.D, CartanMatrix.A, Matrix.of_apply]
      decide) (by decide)
  exact ⟨by decide, ⟨e.trans q, hq⟩, hstar⟩

/-- The distinguished tips of outer D3 become A3's endpoints; the full image is exact. -/
theorem hasRankOneOuterAIndex_three_of_D_three (e : d.Vertex ≃ Fin 3)
    (h : d.IsNumberingOf (CartanMatrix.D 3) (fun i => i.val = 1 ∨ i.val = 2) e)
    (hnot : ¬ d.StarIsTrivial) : d.HasRankOneOuterAIndex 3 := by
  let q : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  have hq : d.IsNumberingOf (CartanMatrix.A 3)
      (fun i => i.val = 0 ∨ i.val + 1 = 3) (e.trans q) :=
    h.relabel q (by
      simp only [CartanMatrix.D, CartanMatrix.A, Matrix.of_apply]
      decide) (by decide)
  exact ⟨Or.inr rfl, e.trans q, hq,
    starImagePair_of_small_A (Or.inr rfl) (e.trans q) hq.1 hnot⟩

end TitsIndexData

end Langlands.GroupScheme
