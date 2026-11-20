import Langlands.Global.RankinSelberg.RealGodementKernelDescent
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentInvolution

/-! # Fourier reflection on the actual real Godement quotient -/

noncomputable section

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg Langlands.RankinSelberg.TwoBlockFirstBlockLaurent
open Langlands.QuotientIntegration Langlands.Whittaker
open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped ENNReal NNReal SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

local instance (t : ℕ) : MeasurableSpace (Langlands.GeneralLinear (t + 1) ℝ) := borel _
local instance (t : ℕ) : BorelSpace (Langlands.GeneralLinear (t + 1) ℝ) := ⟨rfl⟩
local instance (t : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent (t + 1) ℝ) := borel _
local instance (t : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (t + 1) ℝ) := ⟨rfl⟩
local instance (t : ℕ) : MeasurableSpace (LeftUnipotentQuotient t ℝ) := borel _
local instance (t : ℕ) : BorelSpace (LeftUnipotentQuotient t ℝ) := ⟨rfl⟩

variable {t : ℕ}

local notation "G" => Langlands.GeneralLinear (t + 1) ℝ

/-- The real Weyl reflection preserves the supplied compatible quotient measure. -/
theorem measurePreserving_realQuotientReflection (D : RealQuotientMeasureData t) :
    MeasurePreserving (reflectionQuotient t) D.measure D.measure := by
  let N := GeneralLinear.upperUnipotent (t + 1) ℝ
  have hN : IsClosed (N : Set G) := UpperUnipotent.isClosed
  let _ : LocallyCompactSpace (Matrix (Fin (t + 1)) (Fin (t + 1)) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin (t + 1) → Fin (t + 1) → ℝ))
  let _ : LocallyCompactSpace G := Units.isOpenEmbedding_val.locallyCompactSpace
  let _ : SecondCountableTopology G := Units.isOpenEmbedding_val.isInducing.secondCountableTopology
  let _ : PseudoMetrizableSpace G := Units.isOpenEmbedding_val.isInducing.pseudoMetrizableSpace
  let _ : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let _ : PseudoMetrizableSpace N := hN.isClosedEmbedding_subtypeVal.isInducing.pseudoMetrizableSpace
  let _ : SigmaCompactSpace N := hN.isClosedEmbedding_subtypeVal.sigmaCompactSpace
  let := D.groupHaar_isHaar
  let := D.unipotentHaar_isHaar
  let := D.unipotentHaar_rightInvariant
  let _ : D.groupHaar.Regular :=
    Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure D.groupHaar
  let _ : D.unipotentHaar.Regular :=
    Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure D.unipotentHaar
  have hmap := IsCompatible.map_quotientAutomorphism N hN
    (reflectionAut t) (reflectionAut_mem_iff t) D.compatible
  rw [mulEquivHaarChar_eq_one_of_involutive (reflectionAut t) (reflectionAut_involutive t),
    mulEquivHaarChar_eq_one_of_involutive _ (fun u => Subtype.ext (reflectionAut_involutive t u.val)),
    div_one, ENNReal.coe_one, one_smul] at hmap
  exact (D.compatible.right_invariant (weylLong (t + 1) ℝ)).comp
    ⟨(quotientAutomorphism N (reflectionAut t) (reflectionAut_mem_iff t)).continuous.measurable, hmap⟩

/-- The actual Weyl-reflected coefficient has the opposite unipotent law. -/
theorem KernelWhittakerLaw.dual {a : ℝˣ} {W : G → ℂ} (hW : KernelWhittakerLaw a W) :
    KernelWhittakerLaw (-a) (ArchimedeanLocal.dualFunction (t + 1) W) := by
  intro u k
  change W (weylInverseTranspose (t + 1) ℝ (u.val * k)) =
    (standardCharacter (realScaledCharacter (-(-a))) t u : ℂ) *
      W (weylInverseTranspose (t + 1) ℝ k)
  have hχ : standardCharacter (realScaledCharacter (-a)) t (reflectedUnipotent u) =
      standardCharacter (realScaledCharacter a) t u := by
    rw [standardCharacter_reflected]
    change (standardCharacter (realScaledCharacter (-a)) t u)⁻¹ = _
    rw [standardCharacter_realScaled_neg, inv_inv]
  rw [weylInverseTranspose_left_unipotent, hW, hχ, neg_neg]

/-- In the positive Fourier convention, the two Godement quotient integrals
have the same absolute convergence and agree with the exact Weyl sign factor. -/
def RealGodementQuotientReflectionStatement : Prop :=
  ∀ (t : ℕ) (a : ℝˣ) (c : RealCharacterData) (D : RealQuotientMeasureData t)
    (Φ : 𝓢(Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ, ℂ))
    (W : Langlands.GeneralLinear (t + 1) ℝ → ℂ) (hW : KernelWhittakerLaw a W)
    (g : Langlands.GeneralLinear (t + 2) ℝ),
    let f := quotientKernel a Φ W hW c (weylInverseTranspose (t + 2) ℝ g)
    let f' := quotientKernel (-a) (realRectangularSchwartzFourier a Φ)
      (ArchimedeanLocal.dualFunction (t + 1) W) hW.dual c.inverse g
    (Integrable f D.measure ↔ Integrable f' D.measure) ∧
      (∫ q, f q ∂D.measure) = (c.character ((-1 : ℝˣ) ^ (t + 1)) : ℂ) * ∫ q, f' q ∂D.measure

theorem realGodementQuotientReflection : RealGodementQuotientReflectionStatement := by
  intro t a c D Φ W hW g f f'
  let sign := c.character ((-1 : ℝˣ) ^ (t + 1))
  let τ := reflectionQuotient (K := ℝ) t
  have hτ := measurePreserving_realQuotientReflection D
  have he : f = fun q : LeftUnipotentQuotient t ℝ => (sign : ℂ) * f' (τ q) := by
    funext q
    induction q using Quotient.inductionOn with
    | h k =>
      dsimp only [f, f', τ, sign]
      rw [reflectionQuotient_mk, quotientKernel_mk, quotientKernel_mk]
      exact realGodementKernelReflection (t + 1) a c Φ W g k
  constructor
  · rw [he, integrable_const_mul_iff sign.isUnit]
    exact hτ.integrable_comp_emb τ.toMeasurableEquiv.measurableEmbedding
  · rw [he, integral_const_mul]
    congr 1
    exact hτ.integral_comp τ.toMeasurableEquiv.measurableEmbedding f'

end Langlands.Global.RankinSelbergGlobal.RealGodement
