import Langlands.LinearAlgebra.SubmoduleFinrank
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Counting restricted weights in a signed integral basis -/

noncomputable section

namespace Langlands.GroupScheme.SignedWeightCount

open Module
open scoped BigOperators

variable {L ι : Type*} [AddCommGroup L]

/-- The signed vector corresponding to a basis index and a unit of `ℤ`. -/
def signedWeight (b : Basis ι ℤ L) (p : ι × ℤˣ) : L :=
  (p.2 : ℤ) • b p.1

/-- Distinct signed basis indices give distinct weights. -/
theorem signedWeight_injective (b : Basis ι ℤ L) :
    Function.Injective (signedWeight b) := by
  classical
  intro p q hpq
  have h := congrArg b.repr hpq
  simp only [signedWeight, map_smul, Basis.repr_self, Finsupp.smul_single,
    smul_eq_mul, mul_one] at h
  rcases (Finsupp.single_eq_single_iff _ _ _ _).mp h with ⟨hindex, hunit⟩ | ⟨hzero, _⟩
  · exact Prod.ext hindex (Units.ext hunit)
  · exact (Units.ne_zero p.2 hzero).elim

/-- Signed basis weights are nonzero. -/
theorem signedWeight_ne_zero (b : Basis ι ℤ L) (p : ι × ℤˣ) :
    signedWeight b p ≠ 0 := by
  intro h
  have h' := congrArg (fun x => b.repr x p.1) h
  simp [signedWeight] at h'

/-- The finite set of all signed basis vectors. -/
def signedWeights [Fintype ι] (b : Basis ι ℤ L) : Finset L := by
  classical
  exact Finset.univ.image (signedWeight b)

theorem zero_not_mem_signedWeights [Fintype ι] (b : Basis ι ℤ L) :
    0 ∉ signedWeights b := by
  classical
  rintro h
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp h
  exact signedWeight_ne_zero b p hp

/-- Multiplicity-one signed weights satisfying a linear equation are counted by
the signed pairs satisfying that equation. -/
theorem sum_signedWeights [Fintype ι] (b : Basis ι ℤ L) (d : L → ℕ)
    (hmult : ∀ p, d (signedWeight b p) = 1) (f : L →ₗ[ℤ] ℤ) (c : ℤ) :
    (∑ x ∈ signedWeights b, if f x = c then d x else 0) =
      Nat.card {p : ι × ℤˣ // (p.2 : ℤ) * f (b p.1) = c} := by
  classical
  rw [signedWeights, Finset.sum_image]
  · simp_rw [hmult]
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype,
      Finset.card_filter, signedWeight, map_smul, smul_eq_mul]
  · intro p _ q _ h
    exact signedWeight_injective b h

variable [DecidableEq L]

/-- Inserting weight zero contributes its multiplicity exactly in degree zero. -/
theorem sum_insert_zero_signedWeights [Fintype ι] (b : Basis ι ℤ L) (d : L → ℕ)
    (hmult : ∀ p, d (signedWeight b p) = 1) (f : L →ₗ[ℤ] ℤ) (c : ℤ) :
    (∑ x ∈ insert 0 (signedWeights b), if f x = c then d x else 0) =
      Nat.card {p : ι × ℤˣ // (p.2 : ℤ) * f (b p.1) = c} +
        if c = 0 then d 0 else 0 := by
  classical
  rw [Finset.sum_insert (zero_not_mem_signedWeights b), sum_signedWeights b d hmult]
  simp only [map_zero]
  simp only [eq_comm (a := (0 : ℤ)), Nat.add_comm]

/-- A finite support consisting of the signed basis weights and possibly zero has
the expected count after restriction along an integer linear functional. -/
theorem sum_filter_eq_signed_card_add_zero [Fintype ι] (T : Finset L)
    (b : Basis ι ℤ L) (d : L → ℕ)
    (hsupport : T.erase 0 = signedWeights b)
    (hzero : 0 ∉ T → d 0 = 0)
    (hmult : ∀ p, d (signedWeight b p) = 1) (f : L →ₗ[ℤ] ℤ) (c : ℤ) :
    (∑ x ∈ T.filter (fun x => f x = c), d x) =
      Nat.card {p : ι × ℤˣ // (p.2 : ℤ) * f (b p.1) = c} +
        if c = 0 then d 0 else 0 := by
  classical
  have hT : insert 0 T = insert 0 (signedWeights b) := by
    rw [← hsupport]
    ext x
    by_cases hx : x = 0 <;> simp [hx]
  have hsum :
      (∑ x ∈ insert 0 T, if f x = c then d x else 0) =
        ∑ x ∈ T, if f x = c then d x else 0 := by
    by_cases h0 : 0 ∈ T
    · rw [Finset.insert_eq_of_mem h0]
    · rw [Finset.sum_insert h0, hzero h0]
      simp
  rw [Finset.sum_filter, ← hsum, hT]
  exact sum_insert_zero_signedWeights b d hmult f c

section Subspaces

variable {K V α : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Dimensions of independent signed weight spaces restricted along a functional
are the signed-pair count plus the zero-weight dimension in degree zero. -/
theorem finrank_biSup_eq_signed_card_add_zero [Fintype ι] (T : Finset L)
    (b : Basis ι ℤ L) (W : L → Submodule K V) (hW : iSupIndep W)
    (hsupport : T.erase 0 = signedWeights b)
    (hzero : 0 ∉ T → W 0 = ⊥)
    (hmult : ∀ p, finrank K (W (signedWeight b p)) = 1)
    (f : L →ₗ[ℤ] ℤ) (c : ℤ) :
    finrank K ↥(⨆ x ∈ T.filter (fun x => f x = c), W x) =
      Nat.card {p : ι × ℤˣ // (p.2 : ℤ) * f (b p.1) = c} +
        if c = 0 then finrank K (W 0) else 0 := by
  rw [Langlands.Plancherel.finrank_biSup_eq_sum hW]
  apply sum_filter_eq_signed_card_add_zero T b (fun x => finrank K (W x))
    hsupport _ hmult f c
  intro h0
  simp [hzero h0]

/-- For a spanning signed decomposition, the zero-weight dimension is the ambient
dimension minus twice the number of basis weights. -/
theorem finrank_zero_eq_sub [Fintype ι] (T : Finset L) (b : Basis ι ℤ L)
    (W : L → Submodule K V) (hW : iSupIndep W)
    (hspan : (⨆ x ∈ T, W x) = ⊤)
    (hsupport : T.erase 0 = signedWeights b)
    (hzero : 0 ∉ T → W 0 = ⊥)
    (hmult : ∀ p, finrank K (W (signedWeight b p)) = 1) :
    finrank K (W 0) = finrank K V - 2 * Fintype.card ι := by
  have h := finrank_biSup_eq_signed_card_add_zero T b W hW hsupport hzero hmult
    (0 : L →ₗ[ℤ] ℤ) 0
  have hfilter : T.filter (fun x => (0 : L →ₗ[ℤ] ℤ) x = 0) = T := by
    ext x
    simp
  rw [hfilter, hspan] at h
  have htotal : finrank K V = 2 * Fintype.card ι + finrank K (W 0) := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_prod, Nat.mul_comm] using h
  rw [htotal, Nat.add_sub_cancel_left]

end Subspaces

end Langlands.GroupScheme.SignedWeightCount
