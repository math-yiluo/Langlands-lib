import Langlands.HarmonicAnalysis.TwoBlockRowFourierCompanionProof
import Langlands.AllField.HarmonicAnalysis.PadicRowFourierEquivarianceProof
import Langlands.AllField.HarmonicAnalysis.TwoBlockRowFourierCompanionStatement
/-!
# Proof of the two-block row Fourier companion identity

The arbitrary-row form of JPSS 1983, (4.8.3), is reduced by full-row Fourier
equivariance under `weylLong * g` and the coordinate reversal of the second block to
a partial Fourier inversion in the first `b` coordinates of the swapped row. That
inversion is proved on joined tensors, using the product decomposition of the row
measure and row Fourier inversion in dimension `b`.
-/

noncomputable section

open MeasureTheory

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement TwoBlockRowFourierCompanionStatement padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling twoBlockRowFourierCompanion
open Langlands.AllField.HarmonicAnalysis

open Langlands.HarmonicAnalysis.TwoBlockRowPartialFourier

namespace TwoBlockRowFourierCompanion
open Langlands.HarmonicAnalysis.TwoBlockRowFourierCompanion
open Langlands.AllField.HarmonicAnalysis.TwoBlockRowFourierCompanion
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement TwoBlockRowFourierCompanionStatement padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling twoBlockRowFourierCompanion
open Langlands.AllField.HarmonicAnalysis

section Measure


end Measure

section General



end General

section Coordinates


end Coordinates

section Weyl


end Weyl

end TwoBlockRowFourierCompanion

open Langlands.HarmonicAnalysis.TwoBlockRowFourierCompanion
open Langlands.AllField.HarmonicAnalysis.TwoBlockRowFourierCompanion

universe uF

/-- The two-block row Fourier companion identity, JPSS 1983, (4.8.3), with arbitrary
fixed rows. -/
theorem twoBlockRowFourierCompanion : TwoBlockRowFourierCompanionStatement.{uF} := by
  intro F _ _ _ _
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  have : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
  have : TotallyDisconnectedSpace F := by
    let : NonarchimedeanRing F := by
      convert! ValuativeRel.nonarchimedeanRing F
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  intro ψ μ hsd a b _ _
  obtain ⟨hσ, -⟩ := scalarFourierClosure F ψ μ hsd
  have hcompat (d : ℕ) := rowFourierCompatibility ψ μ d hsd
  refine ⟨(hcompat (a + b)).1, ?_⟩
  intro Φ Φhat hpair g ξ η
  let T := (⟨⟩ : LocalFieldData F)
  let W := Langlands.GeneralLinear.weylLong (a + b) F
  let e : Fin b ⊕ Fin a ≃ Fin (a + b) := contiguousEquiv (Nat.add_comm b a)
  let e' : Fin a ⊕ Fin b ≃ Fin (a + b) := contiguousEquiv rfl
  -- `Ψ = Φ (· (W g))` and `Φg = Φ (· g)` are test functions; `Ψhat` is the Fourier
  -- transform of `Ψ`.
  obtain ⟨⟨Ψ, hΨ⟩, hΨfour⟩ := padicRowFourierEquivariance F T (a + b) ψ μ (W * g) Φ
  obtain ⟨⟨Φg, hΦg⟩, -⟩ := padicRowFourierEquivariance F T (a + b) ψ μ g Φ
  obtain ⟨Ψhat, hΨhat⟩ := (hcompat (a + b)).1 Ψ
  -- `|det (W g)| = |det g| ≠ 0`.
  have hW : T.normalizedAbs (Matrix.det W.val) = 1 := by
    have h1 : Matrix.det W.val * Matrix.det W.val = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, Langlands.GeneralLinear.weylLong_mul_self,
        Units.val_one, Matrix.det_one]
    have h2 := congrArg T.normalizedAbs h1
    rw [T.normalizedAbs_mul, T.normalizedAbs_one] at h2
    nlinarith [T.normalizedAbs_nonneg (Matrix.det W.val)]
  have hdet :
      T.normalizedAbs (Matrix.det (W * g).val) = T.normalizedAbs (Matrix.det g.val) := by
    rw [Units.val_mul, Matrix.det_mul, T.normalizedAbs_mul, hW, one_mul]
  have hdetg : Matrix.det g.val ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det g.val).mp g.isUnit).ne_zero
  have hc0 : (T.normalizedAbs (Matrix.det g.val) : ℂ) ≠ 0 := by
    exact_mod_cast (T.normalizedAbs_pos hdetg).ne'
  have hM : ((W * g)⁻¹).val.transpose =
      (W * Langlands.GeneralLinear.inverseTranspose (a + b) F g).val := by
    rw [← Langlands.GeneralLinear.inverseTranspose_coe, map_mul,
      Langlands.GeneralLinear.inverseTranspose_weylLong]
  -- The left integrand is `|det g|` times the inverse-character integrand of `Ψhat`.
  have hΦhat (y : Fin (a + b) → F) :
      Φhat (Matrix.vecMul y
        (W * Langlands.GeneralLinear.inverseTranspose (a + b) F g).val) =
        (T.normalizedAbs (Matrix.det g.val) : ℂ) * Ψhat y := by
    rw [hΨhat y, hΨfour Ψ hΨ y, hdet, hM, ← hpair, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  have hLfun : (fun u : Fin b → F =>
      ψ.complex (-rowPairing u ξ) *
        Φhat (Matrix.vecMul (twoBlockSwappedRow u η)
          (W * Langlands.GeneralLinear.inverseTranspose (a + b) F g).val)) =
      fun u => (T.normalizedAbs (Matrix.det g.val) : ℂ) *
        (ψ.complex (rowPairing u (-ξ)) * slice e Ψhat η u) := by
    funext u
    rw [hΦhat, slice_apply, twoBlockSwappedRow_eq_join, rowPairing_neg_right]
    ring
  -- The right integrand is the Fourier integrand of a slice of `Φg`.
  have hRfun : (fun w : Fin a → F =>
      ψ.complex (rowPairing w (η ∘ Fin.rev)) *
        Φ (Matrix.vecMul (Fin.append w (ξ ∘ Fin.rev)) g.val)) =
      fun w => ψ.complex (rowPairing w (η ∘ Fin.rev)) * slice e' Φg (ξ ∘ Fin.rev) w := by
    funext w
    rw [slice_apply, hΦg, join_contiguousEquiv]
    rfl
  -- After the reversal `v = w ∘ rev`, the right integrand is the plus-character
  -- integrand of `Ψ` in the second block of the swapped row.
  have hΨrev (w : Fin a → F) :
      ψ.complex (rowPairing (w ∘ Fin.rev) η) * Ψ (join e ξ (w ∘ Fin.rev)) =
        ψ.complex (rowPairing w (η ∘ Fin.rev)) *
          Φ (Matrix.vecMul (Fin.append w (ξ ∘ Fin.rev)) g.val) := by
    rw [rowPairing_comp_rev, hΨ, Units.val_mul, ← Matrix.vecMul_vecMul,
      ← twoBlockSwappedRow_eq_join, vecMul_weylLong, twoBlockSwappedRow_comp_rev]
  refine ⟨?_, ?_, ?_⟩
  · rw [hLfun]
    exact (schwartz_rowFourierIntegrand_integrable ψ μ (slice e Ψhat η) (-ξ)).const_mul _
  · rw [hRfun]
    exact schwartz_rowFourierIntegrand_integrable ψ μ (slice e' Φg (ξ ∘ Fin.rev)) (η ∘ Fin.rev)
  · rw [hLfun, integral_const_mul, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
    simp only [slice_apply, rowPairing_neg_right]
    rw [integral_join_rowFourierPair ψ μ (hcompat b).2 e Ψ Ψhat hΨhat ξ η]
    refine (integral_comp_rev μ
      (fun v => ψ.complex (rowPairing v η) * Ψ (join e ξ v))).symm.trans ?_
    exact integral_congr_ae (Filter.Eventually.of_forall hΨrev)

end Langlands.AllField.HarmonicAnalysis
