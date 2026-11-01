import Langlands.Representation.RankinSelberg.TwoBlockLowerUnipotentQuotientData
import Langlands.Representation.Whittaker.DualTransform
import Langlands.Analysis.Local.QuotientAutomorphismStatement
import Langlands.LocalField.Normalization.Proof

/-! # Actual quotient geometry for lower Fourier transport -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockLowerFourier

open GeneralLinear TwoBlockJacquet TwoBlockDeformation
  TwoBlockLowerUnipotentQuotient QuotientIntegration Whittaker

universe uR uF

section Algebra

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable (R : Type uR) [CommRing R]

set_option maxHeartbeats 1000000 in
/-- Reversing the two blocks inverts their rotation. -/
theorem blockRotation_reverse :
    blockRotation (reverse_sum h) R = (blockRotation h R)⁻¹ := by
  rw [blockRotation_eq_permutation, blockRotation_inv]
  unfold BlockShape.reverseMatrix
  congr 1
  apply Equiv.ext
  intro k
  obtain ⟨i, a, rfl⟩ := exists_index_eq (reverse_sum h) k
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · rw [reversePermutation_symm_index_zero]
    trans (succBlockShape m h).index 1 a
    · apply Fin.ext
      rw [val_index_one, val_index_one]
      rfl
    · exact ((succBlockShape m h).reversePermutation_index 0 a).symm
  · rw [reversePermutation_symm_index_one]
    trans (succBlockShape m h).index 0 a
    · apply Fin.ext
      rw [val_index_zero, val_index_zero]
    · exact ((succBlockShape m h).reversePermutation_index 1 a).symm

/-- Permutation rotations are fixed by inverse transpose. -/
theorem inverseTranspose_blockRotation :
    inverseTranspose (t + 1) R (blockRotation h R) = blockRotation h R := by
  rw [blockRotation_eq_permutation, inverseTranspose_permutation]

set_option maxHeartbeats 1000000 in
/-- Long Weyl conjugation inverts the block rotation. -/
theorem weyl_conjugate_blockRotation :
    weylLong (t + 1) R * blockRotation h R * weylLong (t + 1) R =
      (blockRotation h R)⁻¹ := by
  apply Units.ext
  ext k l
  rw [weylLong_conjugate_entry, blockRotation_apply, blockRotation_inv_apply]
  obtain ⟨i, a, rfl⟩ := exists_index_eq h k
  have hp := reversePermutation_symm_index_eq_rev h i a
  have hp' := reversePermutation_symm_index_eq_rev h i a.rev
  rw [Fin.rev_rev] at hp'
  have hiff :
      (succBlockShape m h).reversePermutation.symm l.rev =
          ((succBlockShape m h).index i a).rev ↔
        (succBlockShape m h).reversePermutation l =
          (succBlockShape m h).index i a := by
    constructor
    · intro e
      have e' := (succBlockShape m h).reversePermutation.symm.injective (e.trans hp'.symm)
      have el := congrArg Fin.rev e'
      rw [Fin.rev_rev] at el
      rw [el, ← hp, Equiv.apply_symm_apply]
    · intro e
      have el : l = (succBlockShape m h).reversePermutation.symm
          ((succBlockShape m h).index i a) := by
        rw [← e, Equiv.symm_apply_apply]
      rw [el, hp, Fin.rev_rev]
      exact hp'
  simp only [hiff]

/-- Rotation cancellation for the two actual lower integrands. -/
theorem dual_rotation (g : GeneralLinear (t + 1) R) :
    weylLong (t + 1) R * inverseTranspose (t + 1) R
        (blockRotation (reverse_sum h) R *
          (weylLong (t + 1) R * inverseTranspose (t + 1) R g)) =
      blockRotation h R * g := by
  rw [map_mul, map_mul, inverseTranspose_blockRotation,
    inverseTranspose_weylLong, inverseTranspose_involutive]
  rw [← mul_assoc, ← mul_assoc, weyl_conjugate_blockRotation,
    blockRotation_reverse, inv_inv]

end Algebra

section Topology

variable (R : Type uR) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (t : ℕ)

/-- The reflected inverse-transpose group automorphism. -/
def reflectedGroup : GeneralLinear (t + 1) R ≃ₜ* GeneralLinear (t + 1) R :=
  (inverseTransposeContinuous (t + 1) R).trans
    (permutationConjugation (t + 1) R Fin.revPerm)

@[simp] theorem reflectedGroup_apply (g : GeneralLinear (t + 1) R) :
    reflectedGroup R t g =
      weylLong (t + 1) R * inverseTranspose (t + 1) R g * weylLong (t + 1) R := by
  change weylLong (t + 1) R * inverseTranspose (t + 1) R g *
    (weylLong (t + 1) R)⁻¹ = _
  rw [weylLong_inv]

theorem reflectedGroup_involutive : Function.Involutive (reflectedGroup R t) := by
  intro g
  rw [reflectedGroup_apply, reflectedGroup_apply]
  simp only [map_mul, inverseTranspose_weylLong, inverseTranspose_involutive]
  calc
    _ = (weylLong (t + 1) R * weylLong (t + 1) R) * g *
        (weylLong (t + 1) R * weylLong (t + 1) R) := by
          simp only [mul_assoc]
    _ = g := by rw [weylLong_mul_self, one_mul, mul_one]

theorem reflectedGroup_mem (g : GeneralLinear (t + 1) R) :
    reflectedGroup R t g ∈ upperUnipotent (t + 1) R ↔
      g ∈ upperUnipotent (t + 1) R := by
  constructor
  · intro hg
    have hn := (reflectedUnipotent ⟨reflectedGroup R t g, hg⟩).property
    change reflectedGroup R t (reflectedGroup R t g) ∈ _ at hn
    rw [reflectedGroup_involutive R t g] at hn
    exact hn
  · intro hg
    exact (reflectedUnipotent ⟨g, hg⟩).property

/-- Standard quotient duality, as automorphism followed by right Weyl translation. -/
def standardDuality :
    LeftQuotient (upperUnipotent (t + 1) R) ≃ₜ
      LeftQuotient (upperUnipotent (t + 1) R) :=
  (quotientAutomorphism (upperUnipotent (t + 1) R)
    (reflectedGroup R t) (reflectedGroup_mem R t)).trans
      (rightTranslate _ (weylLong (t + 1) R))

@[simp] theorem standardDuality_mk (g : GeneralLinear (t + 1) R) :
    standardDuality R t (Quotient.mk _ g) =
      Quotient.mk _ (weylLong (t + 1) R * inverseTranspose (t + 1) R g) := by
  simp only [standardDuality, Homeomorph.trans_apply, quotientAutomorphism_mk,
    rightTranslate_mk, reflectedGroup_apply, mul_assoc, weylLong_mul_self, mul_one]

theorem standardDuality_involutive : Function.Involutive (standardDuality R t) := by
  intro q
  induction q using Quotient.inductionOn with
  | h g =>
    simp only [standardDuality_mk, map_mul, inverseTranspose_weylLong,
      inverseTranspose_involutive, ← mul_assoc, weylLong_mul_self, one_mul]

@[simp] theorem standardDuality_symm_mk (g : GeneralLinear (t + 1) R) :
    (standardDuality R t).symm (Quotient.mk _ g) =
      Quotient.mk _ (weylLong (t + 1) R * inverseTranspose (t + 1) R g) := by
  rw [Homeomorph.symm_apply_eq]
  exact ((standardDuality_involutive R t) _).symm.trans
    (congrArg (standardDuality R t) (standardDuality_mk R t g))

variable {t}
variable {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The uniform homeomorphism between the two actual lower quotients. -/
def lowerDuality : LowerQuotient h R ≃ₜ LowerQuotient (reverse_sum h) R :=
  ((lowerToStandardHomeomorph h R).trans (standardDuality R t)).trans
    (lowerToStandardHomeomorph (reverse_sum h) R).symm

@[simp] theorem lowerDuality_mk (g : GeneralLinear (t + 1) R) :
    lowerDuality R h (Quotient.mk _ g) =
      Quotient.mk _ (weylLong (t + 1) R * inverseTranspose (t + 1) R g) := by
  simp only [lowerDuality, Homeomorph.trans_apply, lowerToStandardHomeomorph_apply,
    lowerToStandard_mk, standardDuality_mk]
  change (lowerToStandard (reverse_sum h) R).symm
    (Quotient.mk _ (weylLong (t + 1) R *
      inverseTranspose (t + 1) R (blockRotation h R * g))) = _
  rw [lowerToStandard_symm_mk, map_mul, inverseTranspose_blockRotation,
    blockRotation_reverse, inv_inv]
  apply congrArg (Quotient.mk _)
  have hc := weyl_conjugate_blockRotation h R
  have hc' : blockRotation h R * weylLong (t + 1) R * blockRotation h R =
      weylLong (t + 1) R := by
    calc _ = blockRotation h R *
        (weylLong (t + 1) R * blockRotation h R * weylLong (t + 1) R) *
          weylLong (t + 1) R := by
            simp only [mul_assoc, weylLong_mul_self, mul_one]
         _ = _ := by rw [hc]; group
  simpa only [mul_assoc] using congrArg (fun x => x * inverseTranspose (t + 1) R g) hc'

@[simp] theorem lowerDuality_symm_mk (g : GeneralLinear (t + 1) R) :
    (lowerDuality R h).symm (Quotient.mk _ g) =
      Quotient.mk _ (weylLong (t + 1) R * inverseTranspose (t + 1) R g) := by
  rw [Homeomorph.symm_apply_eq, lowerDuality_mk]
  simp only [map_mul, inverseTranspose_weylLong, inverseTranspose_involutive,
    ← mul_assoc, weylLong_mul_self, one_mul]

theorem lowerDuality_conjugation (q : LeftQuotient (upperUnipotent (t + 1) R)) :
    lowerToStandard (reverse_sum h) R
      (lowerDuality R h ((lowerToStandard h R).symm q)) = standardDuality R t q := by
  change lowerToStandardHomeomorph (reverse_sum h) R
    ((lowerToStandardHomeomorph (reverse_sum h) R).symm
      (standardDuality R t
        (lowerToStandardHomeomorph h R ((lowerToStandardHomeomorph h R).symm q)))) = _
  simp only [Homeomorph.apply_symm_apply]

end Topology

section Orders

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

theorem ord_determinant_weylLong :
    F.canonicalTopologicalData.ord
      (determinant (weylLong (t + 1) F.Carrier) : F.Carrier) = 0 := by
  have hd : (determinant (weylLong (t + 1) F.Carrier) : F.Carrier) *
      (determinant (weylLong (t + 1) F.Carrier) : F.Carrier) = 1 := by
    rw [← Units.val_mul, ← map_mul, weylLong_mul_self, map_one, Units.val_one]
  have hm := F.canonicalTopologicalData.ord_mul
    (determinant (weylLong (t + 1) F.Carrier)).ne_zero
    (determinant (weylLong (t + 1) F.Carrier)).ne_zero
  rw [hd, F.canonicalTopologicalData.ord_one] at hm
  omega

theorem ord_determinant_dual (g : GeneralLinear (t + 1) F.Carrier) :
    F.canonicalTopologicalData.ord
      (determinant (weylLong (t + 1) F.Carrier *
        inverseTranspose (t + 1) F.Carrier g) : F.Carrier) =
      -F.canonicalTopologicalData.ord (determinant g : F.Carrier) := by
  have hi : (determinant (inverseTranspose (t + 1) F.Carrier g) : F.Carrier) =
      (determinant g : F.Carrier)⁻¹ := by
    change Matrix.det (g⁻¹).val.transpose = _
    rw [Matrix.det_transpose]
    simpa only [Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply] using
      congrArg Units.val (map_inv determinant g)
  rw [map_mul, Units.val_mul, F.canonicalTopologicalData.ord_mul
    (determinant _).ne_zero (determinant _).ne_zero,
    ord_determinant_weylLong, zero_add, hi, F.canonicalTopologicalData.ord_inv]

theorem lowerDuality_order :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    ∀ z : LowerQuotient h F.Carrier,
      TwoBlockLowerUnipotentQuotient.determinantOrder F (reverse_sum h) (lowerDuality F.Carrier h z) =
        -TwoBlockLowerUnipotentQuotient.determinantOrder F h z := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  intro z
  induction z using Quotient.inductionOn with
  | h g =>
    rw [lowerDuality_mk, TwoBlockLowerUnipotentQuotient.determinantOrder_mk, TwoBlockLowerUnipotentQuotient.determinantOrder_mk]
    exact ord_determinant_dual F g

theorem lowerDuality_symm_order :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    ∀ z : LowerQuotient (reverse_sum h) F.Carrier,
      TwoBlockLowerUnipotentQuotient.determinantOrder F h ((lowerDuality F.Carrier h).symm z) =
        -TwoBlockLowerUnipotentQuotient.determinantOrder F (reverse_sum h) z := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  intro z
  induction z using Quotient.inductionOn with
  | h g =>
    rw [lowerDuality_symm_mk, TwoBlockLowerUnipotentQuotient.determinantOrder_mk, TwoBlockLowerUnipotentQuotient.determinantOrder_mk]
    exact ord_determinant_dual F g

theorem lowerDuality_slices :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    ∀ k : ℤ,
      lowerDuality F.Carrier h '' TwoBlockLowerUnipotentQuotient.determinantSlice F h k =
          TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k) ∧
      lowerDuality F.Carrier h ⁻¹' TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k) =
          TwoBlockLowerUnipotentQuotient.determinantSlice F h k ∧
      (lowerDuality F.Carrier h).symm '' TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k) =
          TwoBlockLowerUnipotentQuotient.determinantSlice F h k ∧
      (lowerDuality F.Carrier h).symm ⁻¹' TwoBlockLowerUnipotentQuotient.determinantSlice F h k =
          TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  intro k
  have hp : lowerDuality F.Carrier h ⁻¹' TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k) =
      TwoBlockLowerUnipotentQuotient.determinantSlice F h k := by
    ext z
    simp only [Set.mem_preimage, TwoBlockLowerUnipotentQuotient.mem_determinantSlice_iff_determinantOrder,
      lowerDuality_order, neg_inj]
  have hps : (lowerDuality F.Carrier h).symm ⁻¹' TwoBlockLowerUnipotentQuotient.determinantSlice F h k =
      TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k) := by
    ext z
    simp only [Set.mem_preimage, TwoBlockLowerUnipotentQuotient.mem_determinantSlice_iff_determinantOrder,
      lowerDuality_symm_order]
    omega
  refine ⟨?_, hp, ?_, hps⟩
  · rw [← hp]
    exact (lowerDuality F.Carrier h).image_preimage _
  · rw [← hps]
    exact (lowerDuality F.Carrier h).symm.image_preimage _

end Orders

end Langlands.RankinSelberg.TwoBlockLowerFourier
