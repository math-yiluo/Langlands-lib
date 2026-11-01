import Langlands.Representation.RankinSelberg.TwoBlockDominantLeviSupport
import Langlands.Representation.RankinSelberg.TwoBlockDominantDualMatrixProof
import Langlands.Representation.RankinSelberg.TwoBlockDominantDualRectangles
import Langlands.Representation.RankinSelberg.DualModels

/-! # Compact first-rectangle support through actual reversed duality -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open GeneralLinear Whittaker HarmonicAnalysis TwoBlockDeformation TwoBlockLowerUnipotentQuotient

universe uF uV

section Algebra

variable {K : Type uF} [Field K] {t : ℕ} {m : Fin 2 → ℕ}

/-- The long reversal exchanges the blocks and reverses their internal indices. -/
theorem reversed_index_rev (h : ∑ i, (m i + 1) = t + 1)
    (i : Fin 2) (a : Fin (m i.rev + 1)) :
    ((succBlockShape (fun i => m i.rev) (reverse_sum h)).index i a).rev =
      (succBlockShape m h).index i.rev a.rev := by
  have hh := TwoBlockJacquet.blockRanks_add h
  fin_cases i
  · change ((succBlockShape (fun i => m i.rev) (reverse_sum h)).index 0 a).rev =
      (succBlockShape m h).index 1 a.rev
    erw [TwoBlockJacquet.index_zero, TwoBlockJacquet.index_one]
    apply Fin.ext
    change t + 1 - (a.val + 1) = m 0 + 1 + (m 1 + 1 - (a.val + 1))
    have ha : a.val < m 1 + 1 := a.isLt
    omega
  · change ((succBlockShape (fun i => m i.rev) (reverse_sum h)).index 1 a).rev =
      (succBlockShape m h).index 0 a.rev
    erw [TwoBlockJacquet.index_one, TwoBlockJacquet.index_zero]
    apply Fin.ext
    change t + 1 - (m 1 + 1 + a.val + 1) = m 0 + 1 - (a.val + 1)
    omega

/-- The actual reflected inverse-transpose Levi blocks. -/
def reflectedLevi (h : ∑ i, (m i + 1) = t + 1)
    (b : (succBlockShape m h).Levi K) :
    (succBlockShape (fun i => m i.rev) (reverse_sum h)).Levi K :=
  fun i => weylLong (m i.rev + 1) K *
    inverseTranspose (m i.rev + 1) K (b i.rev) * weylLong (m i.rev + 1) K

/-- Reflected inverse transpose of the actual Levi embedding. -/
theorem weyl_inverseTranspose_levi (h : ∑ i, (m i + 1) = t + 1)
    (b : (succBlockShape m h).Levi K) :
    weylLong (t + 1) K *
        inverseTranspose (t + 1) K ((succBlockShape m h).leviEmbedding K b) *
        weylLong (t + 1) K =
      (succBlockShape (fun i => m i.rev) (reverse_sum h)).leviEmbedding K
        (reflectedLevi h b) := by
  apply Units.ext
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ :=
    (succBlockShape (fun i => m i.rev) (reverse_sum h)).indexEquiv.surjective x
  obtain ⟨⟨l, d⟩, rfl⟩ :=
    (succBlockShape (fun i => m i.rev) (reverse_sum h)).indexEquiv.surjective y
  change (weylLong (t + 1) K *
      inverseTranspose (t + 1) K ((succBlockShape m h).leviEmbedding K b) *
      weylLong (t + 1) K).val
      ((succBlockShape (fun i => m i.rev) (reverse_sum h)).index i a)
      ((succBlockShape (fun i => m i.rev) (reverse_sum h)).index l d) =
    ((succBlockShape (fun i => m i.rev) (reverse_sum h)).leviEmbedding K
      (reflectedLevi h b)).val
      ((succBlockShape (fun i => m i.rev) (reverse_sum h)).index i a)
      ((succBlockShape (fun i => m i.rev) (reverse_sum h)).index l d)
  rw [weylLong_conjugate_entry, inverseTranspose_entry,
    reversed_index_rev h, reversed_index_rev h, ← map_inv]
  by_cases hil : i = l
  · subst l
    rw [BlockShape.leviEmbedding_apply_same, BlockShape.leviEmbedding_apply_same]
    simp only [reflectedLevi, weylLong_conjugate_entry, inverseTranspose_entry, Pi.inv_apply]
  · rw [(succBlockShape m h).leviEmbedding_apply_ne K _ d.rev a.rev
      (fun he => hil (Fin.rev_injective he.symm)),
      (succBlockShape (fun i => m i.rev) (reverse_sum h)).leviEmbedding_apply_ne
        K _ a d hil]

end Algebra

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

variable {t r j k : ℕ} {m : Fin 2 → ℕ}

/-- One compact set controls the first rectangle in reflected dual coordinates. -/
def IsLeviFirstRectangularSupport
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ell : glFunctionals ψ r π) (W : (coefficientModel π ell).toSubmodule)
    (C : Set (Matrix (Fin k) (Fin (m 0 + 1)) F.Carrier)) : Prop :=
  IsCompact C ∧ ∀ (b : (succBlockShape m h).Levi F.Carrier)
    (c : GeneralLinear (t + 1) F.Carrier)
    (x : Matrix (Fin (m 0 + 1)) (Fin k) F.Carrier)
    (y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier),
    c ∈ integralOpen F t →
    W.val.val (matrix h hr ((succBlockShape m h).leviEmbedding F.Carrier b * c) x y) ≠ 0 →
    (-x.transpose) *
      (weylLong (m 0 + 1) F.Carrier * inverseTranspose (m 0 + 1) F.Carrier (b 0) *
        weylLong (m 0 + 1) F.Carrier).val ∈ C

/-- Actual compact first-rectangle support for every smooth ambient coefficient. -/
theorem exists_levi_first_rectangular_support
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ r π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ C, IsLeviFirstRectangularSupport F ψ h hr π ell W C := by
  let WD := translatedFirstDualModelEquiv ψ π ell (rightWeyl hr) W
  obtain ⟨C, hC, hsupport⟩ :=
    exists_levi_second_rectangular_support F (ψ.scale (-1)) (reverse_sum h)
      (by omega : r = t + (k + j + 1))
      (inverseTransposePullback π) (inverseTransposePullback_isSmooth π hπ)
      (firstDualFunctional ψ π ell) WD
  refine ⟨C, hC, fun b c x y hc hW => ?_⟩
  let cD := weylLong (t + 1) F.Carrier * inverseTranspose (t + 1) F.Carrier c
  have hcD : cD ∈ integralOpen F t :=
    (integralOpen F t).mul_mem (permutation_mem_integralOpen F t Fin.revPerm)
      (TwoBlockDeformation.inverseTranspose_mem_integralOpen F hc)
  have hg :
      (succBlockShape (fun i => m i.rev) (reverse_sum h)).leviEmbedding F.Carrier
          (reflectedLevi h b) * cD =
        weylLong (t + 1) F.Carrier * inverseTranspose (t + 1) F.Carrier
          ((succBlockShape m h).leviEmbedding F.Carrier b * c) := by
    rw [← weyl_inverseTranspose_levi h b, map_mul]
    simp only [cD, mul_assoc]
    rw [← mul_assoc (weylLong (t + 1) F.Carrier) (weylLong (t + 1) F.Carrier),
      weylLong_mul_self, one_mul]
  have hD := hsupport (reflectedLevi h b) cD
    (signedReverseTranspose (m 1 + 1) j y) (signedReverseTranspose k (m 0 + 1) x) hcD
  have hWD :
      WD.val.val (matrix (reverse_sum h) (by omega : r = t + (k + j + 1))
        ((succBlockShape (fun i => m i.rev) (reverse_sum h)).leviEmbedding F.Carrier
          (reflectedLevi h b) * cD)
        (signedReverseTranspose (m 1 + 1) j y)
        (signedReverseTranspose k (m 0 + 1) x)) ≠ 0 := by
    rw [hg]
    change W.val.val (weylLong (r + 1) F.Carrier *
      inverseTranspose (r + 1) F.Carrier (reversedMatrix h hr
        (weylLong (t + 1) F.Carrier * inverseTranspose (t + 1) F.Carrier
          ((succBlockShape m h).leviEmbedding F.Carrier b * c))
        (signedReverseTranspose (m 1 + 1) j y)
        (signedReverseTranspose k (m 0 + 1) x))) ≠ 0
    have he := ((twoBlockDominantDualMatrix F.Carrier t r j k m h hr).2
      (signedReverseTranspose (m 1 + 1) j y)
      (signedReverseTranspose k (m 0 + 1) x)).2
      ((succBlockShape m h).leviEmbedding F.Carrier b * c)
    simpa only [he, signedReverseTranspose_apply, Fin.rev_rev, neg_neg] using hW
  have hcoord :
      (signedReverseTranspose k (m 0 + 1) x).submatrix Fin.rev Fin.rev = -x.transpose := by
    ext i l
    simp only [Matrix.submatrix_apply, signedReverseTranspose_apply, Fin.rev_rev,
      Matrix.neg_apply, Matrix.transpose_apply]
  have hresult := hD hWD
  change (signedReverseTranspose k (m 0 + 1) x).submatrix Fin.rev Fin.rev *
    (weylLong (m 0 + 1) F.Carrier * inverseTranspose (m 0 + 1) F.Carrier (b 0) *
      weylLong (m 0 + 1) F.Carrier).val ∈ C at hresult
  rw [hcoord] at hresult
  exact hresult

end Langlands.RankinSelberg.TwoBlockDominantRectangular
