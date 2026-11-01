import Langlands.Representation.RankinSelberg.TwoBlockDominantEndpointBounds
import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstRectangleSupport

/-! # First inverse-endpoint bound through actual reversed duality -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open GeneralLinear Whittaker HarmonicAnalysis TwoBlockDeformation TwoBlockLowerUnipotentQuotient

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

variable {t r j k : ℕ} {m : Fin 2 → ℕ}

/-- The initial entry of the inverse first Levi block is uniformly bounded
on the support of the actual dominant coefficient. -/
def IsLeviFirstInverseEndpointBound
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ell : glFunctionals ψ r π) (W : (coefficientModel π ell).toSubmodule)
    (B : ℝ) : Prop :=
  1 ≤ B ∧ ∀ (b : (succBlockShape m h).Levi F.Carrier)
    (c : GeneralLinear (t + 1) F.Carrier)
    (x : Matrix (Fin (m 0 + 1)) (Fin k) F.Carrier)
    (y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier),
    c ∈ integralOpen F t →
    W.val.val (matrix h hr ((succBlockShape m h).leviEmbedding F.Carrier b * c) x y) ≠ 0 →
    F.canonicalTopologicalData.normalizedAbs ((b 0)⁻¹ 0 0) ≤ B

/-- Every smooth ambient coefficient has an actual first inverse-endpoint bound. -/
theorem exists_levi_first_inverse_endpoint_bound
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ r π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ B, IsLeviFirstInverseEndpointBound F ψ h hr π ell W B := by
  let WD := translatedFirstDualModelEquiv ψ π ell (rightWeyl hr) W
  obtain ⟨B, hB, hsupport⟩ :=
    exists_levi_second_endpoint_bound F (ψ.scale (-1)) (reverse_sum h)
      (by omega : r = t + (k + j + 1))
      (inverseTransposePullback π) (inverseTransposePullback_isSmooth π hπ)
      (firstDualFunctional ψ π ell) WD
  refine ⟨B, hB, fun b c x y hc hW => ?_⟩
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
  have hresult := hD hWD
  change F.canonicalTopologicalData.normalizedAbs
    ((weylLong (m 0 + 1) F.Carrier * inverseTranspose (m 0 + 1) F.Carrier (b 0) *
      weylLong (m 0 + 1) F.Carrier) (Fin.last (m 0)) (Fin.last (m 0))) ≤ B at hresult
  simpa only [weylLong_conjugate_entry, inverseTranspose_entry, Fin.rev_last] using hresult

end Langlands.RankinSelberg.TwoBlockDominantRectangular
