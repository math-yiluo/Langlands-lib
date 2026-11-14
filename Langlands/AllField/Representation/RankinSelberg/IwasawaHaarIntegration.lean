import Langlands.Representation.RankinSelberg.IwasawaHaarIntegration
import Langlands.AllField.Group.GL.BlockModulusSupplement
import Langlands.AllField.Representation.RankinSelberg.DiagonalUnipotentHaar
import Langlands.AllField.Representation.RankinSelberg.IwasawaTorusPartitionProof
/-!
# Iwasawa integration on the whole group `GL_(n+1)`

Haar measure on `GL_(n+1)(F)` is recovered from Borel coordinates
`(a, u) ↦ diag(a) u` and Haar measure restricted to `K = GL_(n+1)(O)`, by the
published factorization integral. Moving the diagonal factor to the right of the
unipotent factor introduces the inverse upper-Borel modulus.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding diagonalConj_map singleton_modulus_real
open Langlands.AllField.RankinSelberg

namespace IwasawaHaar
open Langlands.RankinSelberg.IwasawaHaar hiding integral_generalLinearHaar_iwasawa
open Langlands.AllField.RankinSelberg.IwasawaHaar
open Langlands.RankinSelberg hiding diagonalConj_map singleton_modulus_real
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear

section Algebra



end Algebra

section Measure




end Measure

section Padic

universe uF

/-- **Iwasawa integration on `GL_(n+1)(F)`**, Bochner form, with the
normalizations of `generalLinearHaar_eq_map_iwasawa`:
`∫_G f = ∫_K ∫_A δ(a)⁻¹ ∫_N f(u diag(a) k) du da dk` for integrable `f`. -/
theorem integral_generalLinearHaar_iwasawa 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel Fˣ
    letI : BorelSpace Fˣ := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F)
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    let A := Fin (n + 1) → Fˣ
    let da : Measure A := Measure.pi (fun _ : Fin (n + 1) =>
      localMultiplicativeHaar F)
    let K := Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
    let δ : A → ℝ := fun a =>
      ∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
        T.normalizedAbs ((a i / a j : Fˣ) : F)
    ∀ f : Langlands.GeneralLinear (n + 1) F → ℂ,
      Integrable f (generalLinearHaar F n) →
        ∫ y, f y ∂generalLinearHaar F n =
          ∫ k in (K : Set (Langlands.GeneralLinear (n + 1) F)),
            ∫ a, (((δ a)⁻¹ : ℝ) : ℂ) *
              ∫ u, f (u.val * Iwasawa.diagonalUnits a * k) ∂unipotentHaar F n ∂da
            ∂generalLinearHaar F n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := borel Fˣ
  let : BorelSpace Fˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  intro A da K δ f hf
  have hw : ∀ a, (unipotentHaar F n).map (diagonalConj a) =
      ENNReal.ofReal ((δ a)⁻¹) • unipotentHaar F n := by
    intro a
    rw [diagonalConj_map F T n a, ENNReal.smul_def]
    congr 1
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_inv, singleton_modulus_real F T a]
  have hδ (a : A) : (ENNReal.ofReal ((δ a)⁻¹)).toReal = (δ a)⁻¹ :=
    ENNReal.toReal_ofReal (inv_nonneg.2 (Finset.prod_nonneg fun i _ =>
      Finset.prod_nonneg fun j _ => T.normalizedAbs_nonneg _))
  rw [integral_generalLinearHaar _ hw (fun _ => ENNReal.ofReal_ne_top) f hf]
  simp only [hδ]
  rfl

end Padic

end IwasawaHaar

end Langlands.AllField.RankinSelberg
