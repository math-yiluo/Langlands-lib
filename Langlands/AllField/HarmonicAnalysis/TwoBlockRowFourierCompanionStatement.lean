import Langlands.HarmonicAnalysis.TwoBlockRowFourierCompanionStatement
import Langlands.AllField.Group.GL.PadicSupplement
/-!
# The two-block row Fourier companion identity

This module states, without proof, an arbitrary-row form of the Fourier
identity (4.8.3) of Jacquet, Piatetski-Shapiro and Shalika (1983), printed
p.415, on the actual row space of a canonical p-adic field. Both sides are
the raw Bochner integrals for the product of the supplied scalar Haar measure.
-/

noncomputable section

open MeasureTheory

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding TwoBlockRowFourierCompanionStatement
open Langlands.AllField.HarmonicAnalysis

universe uF

/-- For positive block sizes `a, b` and a self-dual scalar measure, every row test
function on `F^(a+b)` has a test-function Fourier partner, and for every such pair
`Φ, Φhat`, every `g` and all fixed rows `ξ ∈ F^b`, `η ∈ F^a`, the inverse-character
transform of `Φhat` in the first `b` coordinates of the rows `(u, η) w (gᵀ)⁻¹`, times
`|det g|⁻¹`, equals the plus-character transform of `Φ` in the first `a` coordinates
of the rows `(w, ξ ∘ rev) g`, evaluated at `η ∘ rev`. Both integrands are integrable. -/
def TwoBlockRowFourierCompanionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F],
    letI : MeasurableSpace F := borel F
    haveI : BorelSpace F := ⟨rfl⟩
    haveI : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
    haveI : TotallyDisconnectedSpace F := by
      let : NonarchimedeanRing F := by
        convert! ValuativeRel.nonarchimedeanRing F
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    ∀ (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F),
      IsSelfDual ψ μ →
      ∀ (a b : ℕ), 0 < a → 0 < b →
        (∀ Φ : SchwartzBruhat (Fin (a + b) → F),
          ∃ Φhat : SchwartzBruhat (Fin (a + b) → F),
            IsRowFourierPair ψ μ Φ Φhat) ∧
        ∀ Φ Φhat : SchwartzBruhat (Fin (a + b) → F),
          IsRowFourierPair ψ μ Φ Φhat →
          ∀ (g : Langlands.GeneralLinear (a + b) F)
            (ξ : Fin b → F) (η : Fin a → F),
            Integrable
              (fun u : Fin b → F =>
                ψ.complex (-rowPairing u ξ) *
                  Φhat (Matrix.vecMul (twoBlockSwappedRow u η)
                    (Langlands.GeneralLinear.weylLong (a + b) F *
                      Langlands.GeneralLinear.inverseTranspose (a + b) F g).val))
              (rowMeasure μ b) ∧
            Integrable
              (fun w : Fin a → F =>
                ψ.complex (rowPairing w (η ∘ Fin.rev)) *
                  Φ (Matrix.vecMul (Fin.append w (ξ ∘ Fin.rev)) g.val))
              (rowMeasure μ a) ∧
            (((⟨⟩ : LocalFieldData F).normalizedAbs (Matrix.det g.val) : ℂ)⁻¹) *
                ∫ u : Fin b → F,
                  ψ.complex (-rowPairing u ξ) *
                    Φhat (Matrix.vecMul (twoBlockSwappedRow u η)
                      (Langlands.GeneralLinear.weylLong (a + b) F *
                        Langlands.GeneralLinear.inverseTranspose (a + b) F g).val)
                  ∂rowMeasure μ b =
              ∫ w : Fin a → F,
                ψ.complex (rowPairing w (η ∘ Fin.rev)) *
                  Φ (Matrix.vecMul (Fin.append w (ξ ∘ Fin.rev)) g.val)
                ∂rowMeasure μ a

end Langlands.AllField.HarmonicAnalysis
