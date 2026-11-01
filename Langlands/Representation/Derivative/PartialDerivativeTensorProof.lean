import Langlands.Representation.Derivative.PartialDerivativeTensorLocalization
import Langlands.Representation.Derivative.TopLocalizationComparison

/-! # The partial derivative of an exterior tensor product -/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

universe uF uV

/-- Zelevinsky 1980, Proposition 3.7(a), with the actual normalized top
 derivative and naturality in both tensor factors, in every rank. -/
theorem partialDerivativeTensor {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    PartialDerivativeTensorStatement.{uF,uV} F T := by
  let _ := T.topology
  intro ψ k m
  exact ⟨PartialTensor.localizationTensorIso ψ.complex k m ≪≫
    Functor.isoWhiskerRight
      (NatIso.prod (Iso.refl (𝟭 _)) (TopLocalization.topLocalizationIso T ψ m))
      PartialTensor.firstFactorFunctor⟩

end Langlands.Derivative
