import Langlands.HarmonicAnalysis.RowFourier
import Langlands.Group.GL.Maps
import Langlands.LocalField.Normalization.Definitions
import Langlands.LocalField.Topology
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-!
# The two-block row Fourier companion identity

This module states, without proof, an arbitrary-row form of the Fourier
identity (4.8.3) of Jacquet, Piatetski-Shapiro and Shalika (1983), printed
p.415, on the actual row space of a canonical p-adic field. Both sides are
the raw Bochner integrals for the product of the supplied scalar Haar measure.
-/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis

universe uF

/-- The row `(u, η)` of length `b + a`, with the `b` coordinates of `u` first,
read in the coordinates of `Fin (a + b)` through `finCongr (Nat.add_comm a b)`. -/
abbrev twoBlockSwappedRow {X : Type*} {a b : ℕ} (u : Fin b → X) (η : Fin a → X) :
    Fin (a + b) → X :=
  fun j => Fin.append u η (finCongr (Nat.add_comm a b) j)

/-- For positive block sizes `a, b` and a self-dual scalar measure, every row test
function on `F^(a+b)` has a test-function Fourier partner, and for every such pair
`Φ, Φhat`, every `g` and all fixed rows `ξ ∈ F^b`, `η ∈ F^a`, the inverse-character
transform of `Φhat` in the first `b` coordinates of the rows `(u, η) w (gᵀ)⁻¹`, times
`|det g|⁻¹`, equals the plus-character transform of `Φ` in the first `a` coordinates
of the rows `(w, ξ ∘ rev) g`, evaluated at `η ∘ rev`. Both integrands are integrable. -/
def TwoBlockRowFourierCompanionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    haveI : BorelSpace F.Carrier := ⟨rfl⟩
    haveI : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
    haveI : TotallyDisconnectedSpace F.Carrier := by
      let : NonarchimedeanRing F.Carrier := by
        convert! ValuativeRel.nonarchimedeanRing F.Carrier
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier),
      IsSelfDual ψ μ →
      ∀ (a b : ℕ), 0 < a → 0 < b →
        (∀ Φ : SchwartzBruhat (Fin (a + b) → F.Carrier),
          ∃ Φhat : SchwartzBruhat (Fin (a + b) → F.Carrier),
            IsRowFourierPair ψ μ Φ Φhat) ∧
        ∀ Φ Φhat : SchwartzBruhat (Fin (a + b) → F.Carrier),
          IsRowFourierPair ψ μ Φ Φhat →
          ∀ (g : Langlands.GeneralLinear (a + b) F.Carrier)
            (ξ : Fin b → F.Carrier) (η : Fin a → F.Carrier),
            Integrable
              (fun u : Fin b → F.Carrier =>
                ψ.complex (-rowPairing u ξ) *
                  Φhat (Matrix.vecMul (twoBlockSwappedRow u η)
                    (Langlands.GeneralLinear.weylLong (a + b) F.Carrier *
                      Langlands.GeneralLinear.inverseTranspose (a + b) F.Carrier g).val))
              (rowMeasure μ b) ∧
            Integrable
              (fun w : Fin a → F.Carrier =>
                ψ.complex (rowPairing w (η ∘ Fin.rev)) *
                  Φ (Matrix.vecMul (Fin.append w (ξ ∘ Fin.rev)) g.val))
              (rowMeasure μ a) ∧
            ((F.canonicalTopologicalData.normalizedAbs (Matrix.det g.val) : ℂ)⁻¹) *
                ∫ u : Fin b → F.Carrier,
                  ψ.complex (-rowPairing u ξ) *
                    Φhat (Matrix.vecMul (twoBlockSwappedRow u η)
                      (Langlands.GeneralLinear.weylLong (a + b) F.Carrier *
                        Langlands.GeneralLinear.inverseTranspose (a + b) F.Carrier g).val)
                  ∂rowMeasure μ b =
              ∫ w : Fin a → F.Carrier,
                ψ.complex (rowPairing w (η ∘ Fin.rev)) *
                  Φ (Matrix.vecMul (Fin.append w (ξ ∘ Fin.rev)) g.val)
                ∂rowMeasure μ a

end Langlands.HarmonicAnalysis
