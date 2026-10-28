import Langlands.Representation.RankinSelberg.UnequalRankComplementaryConjugationStatement

/-!
# Proof of complementary lower-row conjugation and translated-dual equivariance

This module proves `UnequalRankComplementaryConjugationStatement`. The unsigned
block Weyl element `blockWeylAt n r` is the permutation matrix of the tail
reversal `tailRev n r`, which fixes `i < n + 1` and sends `i ≥ n + 1` to
`r + n + 1 - i`. Hence the `(p, q)` entry of the inverse transpose of
`a⁻¹ * g * a` is the `(tailRev q, tailRev p)` entry of `g⁻¹`. Applied to the
complementary upper column `U(z)`, whose inverse is `1 - E(z)`, this gives the
lower row `L(-z)` entry by entry. Equivariance of the translated first dual
model equivalence then follows by comparing values, using that
`inverseTranspose` is multiplicative.
-/

noncomputable section

universe uF uV

namespace Langlands.RankinSelberg.UnequalRankComplementaryConjugationProof

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis

/-- The block tail reversal of `Fin (r + 1)`: it fixes `i < n + 1` and sends
`i ≥ n + 1` to `r + n + 1 - i`. -/
def tailRev (n r : ℕ) (i : Fin (r + 1)) : Fin (r + 1) :=
  if h : i.val < n + 1 then i else ⟨r + n + 1 - i.val, by omega⟩

/-- The tail reversal fixes the leading indices. -/
theorem tailRev_of_lt (n r : ℕ) {i : Fin (r + 1)} (h : i.val < n + 1) :
    tailRev n r i = i := by
  simp only [tailRev, h, ↓reduceDIte]

/-- The tail reversal reverses the trailing indices. -/
theorem tailRev_val_of_ge (n r : ℕ) {i : Fin (r + 1)} (h : ¬ i.val < n + 1) :
    (tailRev n r i).val = r + n + 1 - i.val := by
  simp only [tailRev, h, ↓reduceDIte]

/-- The tail reversal is an involution. -/
theorem tailRev_involutive (n r : ℕ) :
    Function.Involutive (tailRev n r) := by
  intro i
  by_cases hi : i.val < n + 1
  · rw [tailRev_of_lt n r hi, tailRev_of_lt n r hi]
  · have h1 := tailRev_val_of_ge n r hi
    have h2 : ¬ (tailRev n r i).val < n + 1 := by omega
    apply Fin.ext
    rw [tailRev_val_of_ge n r h2]
    omega

/-- The tail reversal as a permutation. -/
def tailRevPerm (n r : ℕ) : Equiv.Perm (Fin (r + 1)) :=
  (tailRev_involutive n r).toPerm

/-- The unsigned block Weyl element is the permutation matrix of the tail
reversal. -/
theorem blockWeylAt_eq (F : Type uF) [Field F] (n r : ℕ) (hnr : n < r) :
    blockWeylAt (F := F) n r hnr = permutation (r + 1) F (tailRevPerm n r) := by
  apply Units.ext
  ext p q
  rw [permutation_entry]
  change (blockSum ((1 : Langlands.GeneralLinear (n + 1) F), weylLong (r - n) F))
    (Fin.cast (by omega) p) (Fin.cast (by omega) q) = _
  change _ = if tailRev n r q = p then (1 : F) else 0
  have key : ∀ i : Fin (r + 1), (∃ h : i.val < n + 1,
      Fin.cast (show r + 1 = (n + 1) + (r - n) by omega) i =
        Fin.castAdd (r - n) ⟨i.val, h⟩) ∨
      (¬ i.val < n + 1 ∧ ∃ h : i.val - (n + 1) < r - n,
        Fin.cast (show r + 1 = (n + 1) + (r - n) by omega) i =
          Fin.natAdd (n + 1) ⟨i.val - (n + 1), h⟩) := by
    intro i
    by_cases hi : i.val < n + 1
    · exact Or.inl ⟨hi, Fin.ext rfl⟩
    · refine Or.inr ⟨hi, by omega, Fin.ext ?_⟩
      simp only [Fin.val_cast, Fin.val_natAdd]
      omega
  rcases key p with ⟨hp, ep⟩ | ⟨hp, hp', ep⟩ <;>
    rcases key q with ⟨hq, eq⟩ | ⟨hq, hq', eq⟩ <;>
    rw [ep, eq]
  · rw [blockSum_apply_left, tailRev_of_lt n r hq, Units.val_one, Matrix.one_apply]
    by_cases h : q = p
    · subst h
      simp
    · rw [ite_eq_right h, ite_eq_right]
      intro h'
      apply h
      apply Fin.ext
      have h'' := congrArg Fin.val h'
      simp only at h''
      omega
  · have hqv := tailRev_val_of_ge n r hq
    rw [blockSum_apply_left_right]
    split_ifs with h
    · rw [Fin.ext_iff] at h; omega
    · rfl
  · rw [blockSum_apply_right_left, tailRev_of_lt n r hq]
    split_ifs with h
    · rw [Fin.ext_iff] at h; omega
    · rfl
  · have hqv := tailRev_val_of_ge n r hq
    rw [blockSum_apply_right, weylLong_entry]
    have e1 : ((⟨q.val - (n + 1), hq'⟩ : Fin (r - n)).rev = ⟨p.val - (n + 1), hp'⟩) ↔
        tailRev n r q = p := by
      rw [Fin.ext_iff, Fin.ext_iff, Fin.val_rev, hqv]
      simp only
      omega
    by_cases h : tailRev n r q = p
    · rw [ite_eq_left h, ite_eq_left (e1.mpr h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (e1.mp h'))]

/-- The `(p, q)` entry of the inverse transpose of `a⁻¹ * g * a`, for
`a = blockWeylAt n r`, is the `(tailRev q, tailRev p)` entry of `g⁻¹`. -/
theorem conj_entry (F : Type uF) [Field F] (n r : ℕ) (hnr : n < r)
    (g : Langlands.GeneralLinear (r + 1) F) (p q : Fin (r + 1)) :
    inverseTranspose (r + 1) F
        ((blockWeylAt n r hnr)⁻¹ * g * blockWeylAt n r hnr) p q =
      (g⁻¹ : Langlands.GeneralLinear (r + 1) F) (tailRev n r q) (tailRev n r p) := by
  rw [blockWeylAt_eq, map_mul, map_mul, map_inv, inverseTranspose_permutation,
    permutation_inv, mul_assoc, permutation_mul_entry, mul_permutation_entry, inv_inv]
  rfl

/-- Entries of the rectangular argument `Fin.snoc 0 (-z)`: only its last row is
nonzero, and that row is `-z`. -/
theorem snoc_neg_apply (F : Type uF) [Field F] {n j : ℕ} (z : Fin (n + 1) → F)
    (i : Fin (j + 1)) (b : Fin (n + 1)) :
    (Fin.snoc 0 (-z) : Matrix (Fin (j + 1)) (Fin (n + 1)) F) i b =
      if i.val = j then -z b else 0 := by
  simp only [Fin.snoc]
  split_ifs <;> first | (exfalso; omega) | simp

/-- Clause 1: `inverseTranspose (a⁻¹ * U(z) * a) = L(-z)`. -/
theorem matrix_clause (F : Type uF) [Field F] (n j k : ℕ) (z : Fin (n + 1) → F) :
    inverseTranspose (n + ((j + 1) + k + 1) + 1) F
        ((blockWeylAt n (n + ((j + 1) + k + 1)) (by omega))⁻¹ *
          GeneralLinear.reindex
            (finCongr (show n + ((k + 1) + j + 1) + 1 = n + ((j + 1) + k + 1) + 1 by omega))
            (unequalRankSmearingUnipotent n k j z) *
          blockWeylAt n (n + ((j + 1) + k + 1)) (by omega)) =
      rectangularUnipotent (j + 1) k (Fin.snoc 0 (-z)) := by
  apply Units.ext
  ext p q
  rw [conj_entry, ← map_inv]
  change (1 - unequalRankSmearingEntries n k j z) (Fin.cast (by omega) _)
      (Fin.cast (by omega) _) =
    (1 + rectangularEntries (j + 1) k (Fin.snoc 0 (-z))) p q
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply,
    unequalRankSmearingEntries, rectangularEntries, Fin.ext_iff, Fin.val_cast,
    snoc_neg_apply]
  by_cases hqn : q.val < n + 1
  · simp only [tailRev_of_lt _ _ hqn]
    by_cases hpn : p.val < n + 1
    · simp only [tailRev_of_lt _ _ hpn]
      split_ifs <;> first | (exfalso; omega) | simp
    · rw [tailRev_val_of_ge _ _ hpn]
      split_ifs <;> first | (exfalso; omega) | simp
  · have h1 : ¬ (tailRev n (n + ((j + 1) + k + 1)) q).val < n + 1 := by
      rw [tailRev_val_of_ge _ _ hqn]; omega
    simp only [h1, hqn, ↓reduceDIte, sub_zero]
    by_cases hpn : p.val < n + 1
    · simp only [tailRev_of_lt _ _ hpn]
      rw [tailRev_val_of_ge _ _ hqn]
      split_ifs <;> first | (exfalso; omega) | simp
    · rw [tailRev_val_of_ge _ _ hpn, tailRev_val_of_ge _ _ hqn]
      split_ifs <;> first | (exfalso; omega) | simp

/-- Clause 2: the translated first dual model equivalence intertwines right
translation by `L(-z)` with right translation by `U(z)`. -/
theorem equivariance_clause (F : Type uF) [Field F] [TopologicalSpace F]
    [IsTopologicalRing F] (n j k : ℕ)
    (ψ : UnitaryAdditiveCharacter F) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + ((j + 1) + k + 1) + 1) F) V)
    (ℓ : glFunctionals ψ (n + ((j + 1) + k + 1)) π)
    (f : (coefficientModel π ℓ).toSubmodule) (z : Fin (n + 1) → F) :
    translatedFirstDualModelEquiv ψ π ℓ (blockWeylAt n (n + ((j + 1) + k + 1)) (by omega))
        (modelRepresentation π ℓ (rectangularUnipotent (j + 1) k (Fin.snoc 0 (-z))) f) =
      modelRepresentation (inverseTransposePullback π) (firstDualFunctional ψ π ℓ)
        (GeneralLinear.reindex
          (finCongr (show n + ((k + 1) + j + 1) + 1 = n + ((j + 1) + k + 1) + 1 by omega))
          (unequalRankSmearingUnipotent n k j z))
        (translatedFirstDualModelEquiv ψ π ℓ
          (blockWeylAt n (n + ((j + 1) + k + 1)) (by omega)) f) := by
  have hmat := matrix_clause F n j k z
  have e1 : modelRepresentation π ℓ (rectangularUnipotent (j + 1) k (Fin.snoc 0 (-z))) f =
      translateModelEquiv ψ π ℓ (rectangularUnipotent (j + 1) k (Fin.snoc 0 (-z))) f := rfl
  rw [e1]
  apply Subtype.ext
  rw [translatedFirstDualModelEquiv_val]
  have e2 : (modelRepresentation (inverseTransposePullback π) (firstDualFunctional ψ π ℓ)
      (GeneralLinear.reindex
        (finCongr (show n + ((k + 1) + j + 1) + 1 = n + ((j + 1) + k + 1) + 1 by omega))
        (unequalRankSmearingUnipotent n k j z))
      (translatedFirstDualModelEquiv ψ π ℓ
        (blockWeylAt n (n + ((j + 1) + k + 1)) (by omega)) f)).val =
      translateWhittaker (ψ.scale (-1)) _
        (translatedFirstDualModelEquiv ψ π ℓ
          (blockWeylAt n (n + ((j + 1) + k + 1)) (by omega)) f).val
        (GeneralLinear.reindex
          (finCongr (show n + ((k + 1) + j + 1) + 1 = n + ((j + 1) + k + 1) + 1 by omega))
          (unequalRankSmearingUnipotent n k j z)) := rfl
  rw [e2, translatedFirstDualModelEquiv_val]
  apply Subtype.ext
  funext x
  simp only [translateWhittaker_apply, firstDualFunction_apply, translateModelEquiv_val]
  rw [← hmat, mul_assoc, ← map_mul]
  group

end Langlands.RankinSelberg.UnequalRankComplementaryConjugationProof

namespace Langlands.RankinSelberg

open UnequalRankComplementaryConjugationProof

/-- Complementary lower-row conjugation and translated-dual equivariance:
`UnequalRankComplementaryConjugationStatement` holds. -/
theorem unequalRankComplementaryConjugation :
    UnequalRankComplementaryConjugationStatement.{uF, uV} :=
  ⟨fun F _ n j k z => matrix_clause F n j k z,
    fun F _ _ _ n j k ψ V _ _ π ℓ f z => equivariance_clause F n j k ψ V π ℓ f z⟩

end Langlands.RankinSelberg
