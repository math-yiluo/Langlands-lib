import Langlands.Representation.RankinSelberg.HighlyRamified.DualWeightSum
import Langlands.Representation.RankinSelberg.HighlyRamified.LowerRowDual
import Langlands.Representation.RankinSelberg.HighlyRamified.DualPointwise
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement

/-!
# The dual integrand of the smeared test vector

Let `f'` be an inverse Whittaker function on `GL_(m+2)` and `F(g) = χ(det g)⁻¹ ∫ S₂(rev x)
f̃'(g ū_x) dx`, where `S₂` is the restricted finite Fourier transform of the weight `Φ₂` of
(4.4.18) over a set of representatives. Then
`F(w ᵗdiag(B,1)⁻¹) = χ(det w)⁻¹ χ(det B) η(O)^(m+1) Φ₂(-rev B_last) f'(diag(B,1))`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis GeneralLinear

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance dualShellFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance dualShellValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance dualShellLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance dualShellFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance dualShellFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩

variable {m : ℕ}

open Classical in
/-- The restricted finite Fourier transform of `Φ₂` at the reversed row `rev x`. -/
def dualWeightFourier (ψ : UnitaryAdditiveCharacter F.Carrier) (ω : F.Carrierˣ →* ℂˣ)
    (ϖ : F.Carrier) (c f : ℕ) (T : Finset (Fin (m + 1) → F.Carrier))
    (x : Matrix (Fin 1) (Fin (m + 1)) F.Carrier) : ℂ :=
  if ∀ k : Fin (m + 1), x 0 k.rev ∈ (ValuativeRel.valuation F.Carrier).integer then
    ∑ z ∈ T, dualWeight ω ϖ c f z * ψ.complex (∑ k, z k * x 0 k.rev) else 0

/-- The smeared second dual function twisted by `χ⁻¹ ∘ det`:
`g ↦ χ(det g)⁻¹ ∫ S₂(rev x) f̃'(g ū_x) dx`. -/
def twistedSmear (ψ : UnitaryAdditiveCharacter F.Carrier) (η : AdditiveHaarMeasure F.Carrier)
    (χ : F.Carrierˣ →* ℂˣ) (ω : F.Carrierˣ →* ℂˣ) (ϖ : F.Carrier) (c f : ℕ)
    (T : Finset (Fin (m + 1) → F.Carrier))
    (f' : RankinSelberg.InverseWhittakerFunctions ψ (m + 1))
    (g : GeneralLinear (m + 1 + 1) F.Carrier) : ℂ :=
  ((χ (determinant g) : ℂ))⁻¹ *
    ∫ x, dualWeightFourier F ψ ω ϖ c f T x *
      (RankinSelberg.secondDualFunction ψ (m + 1) f').val (g * lowerRow x)
      ∂RankinSelberg.rectangularMeasure η 1 (m + 1)

theorem determinant_weyl_inverseTranspose_rankInclusion (B : GeneralLinear (m + 1) F.Carrier) :
    determinant (weylLong (m + 1 + 1) F.Carrier *
        inverseTranspose (m + 1 + 1) F.Carrier (rankInclusion 1 B)) =
      determinant (weylLong (m + 1 + 1) F.Carrier) * (determinant B)⁻¹ := by
  rw [map_mul, determinant_inverseTranspose]
  congr 2
  apply Units.ext
  simp only [determinant, Matrix.GeneralLinearGroup.val_det_apply]
  exact RankinSelberg.det_rankInclusion 1 _

/-- The twisted smeared function at `w ᵗdiag(B,1)⁻¹`. -/
theorem twistedSmear_at_dual (ψ : UnitaryAdditiveCharacter F.Carrier)
    (η : AdditiveHaarMeasure F.Carrier) (hψ : HasIntegerConductorAt F ψ)
    (χ : F.Carrierˣ →* ℂˣ) {ω : F.Carrierˣ →* ℂˣ} {ϖ : F.Carrier} {c f : ℕ}
    (hf : 0 < f) (hω : TrivialOnPrincipalUnits ω f)
    (hscale : ∀ o ∈ (ValuativeRel.valuation F.Carrier).integer, InPow f (ϖ ^ c * o))
    (T : Finset (Fin (m + 1) → F.Carrier))
    (hT : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ integerLattice F m → t = t')
    (hcov : ∀ y, dualWeight ω ϖ c f y ≠ 0 → ∃ t ∈ T, y - t ∈ integerLattice F m)
    (f' : RankinSelberg.InverseWhittakerFunctions ψ (m + 1)) (B : GeneralLinear (m + 1) F.Carrier) :
    twistedSmear F ψ η χ ω ϖ c f T f'
        (weylLong (m + 1 + 1) F.Carrier * inverseTranspose (m + 1 + 1) F.Carrier
          (rankInclusion 1 B)) =
      ((χ (determinant (weylLong (m + 1 + 1) F.Carrier)) : ℂ))⁻¹ * (χ (determinant B) : ℂ) *
        ((η.measure ((integerAddSubgroup F : AddSubgroup F.Carrier) :
          Set F.Carrier)).toReal : ℂ) ^ (m + 1) *
        dualWeight ω ϖ c f (fun k => -B (Fin.last m) k.rev) * f'.val (rankInclusion 1 B) := by
  unfold twistedSmear
  rw [smearedSecondDual_at_dual ψ f' B _ (dualWeightFourier F ψ ω ϖ c f T)]
  have hint := integral_dualWeight_fourier F ψ η hψ hf hω hscale T hT hcov
    (fun j => B (Fin.last m) j)
  simp only [dualWeightFourier] at hint ⊢
  rw [hint, determinant_weyl_inverseTranspose_rankInclusion, map_mul, map_inv, Units.val_mul,
    Units.val_inv_eq_inv_val, mul_inv, inv_inv]
  ring

end Langlands.RankinSelberg.HighlyRamified
