import Langlands.HarmonicAnalysis.RectangularRho0FourierCovarianceStatement
import Langlands.HarmonicAnalysis.RectangularFourierCovarianceProof
import Langlands.HarmonicAnalysis.RectangularFourierCommutationProof

/-! JPSS Section 6.1 formula (7): the chosen full rectangular Fourier equivalence
carries the transported action `rectangularRho0 g` to the twisted transported action
of the inverse transpose. The proof conjugates the published full covariance theorem
through the chosen last-column Fourier equivalence, which commutes with the full
Fourier equivalence. -/

namespace Langlands.HarmonicAnalysis

universe uK

/-- Full Fourier covariance of the transported action: the chosen full rectangular
Fourier equivalence carries `rectangularRho0 g` to the reciprocal of the `n`-th power
of the intrinsic Haar character of `det g` times `rectangularRho0` of the inverse
transpose of `g`. -/
theorem rectangularRho0FourierCovariance :
    RectangularRho0FourierCovarianceStatement.{uK} := by
  intro K _ _ _ _ _ _ _ _ ψ μ n hsd g Φ
  set F := rectangularFourierEquiv ψ μ n (n + 1) hsd
  set T := partialFourierEquiv ψ μ n hsd
  have hcomm : ∀ Ψ, F (T Ψ) = T (F Ψ) := rectangularFourierCommutation ψ μ n hsd
  -- Commutation with `T` gives commutation with `T.symm`.
  have hcommSymm : ∀ Ψ, F (T.symm Ψ) = T.symm (F Ψ) := by
    intro Ψ
    apply T.injective
    rw [← hcomm, T.apply_symm_apply, T.apply_symm_apply]
  rw [rectangularRho0_apply, rectangularRho0_apply, hcomm,
    rectangularFourierCovariance ψ μ n (n + 1) hsd g, hcommSymm, map_smul]

end Langlands.HarmonicAnalysis
