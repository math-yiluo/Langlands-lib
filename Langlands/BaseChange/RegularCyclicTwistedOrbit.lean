import Langlands.BaseChange.CyclicNormFieldConjugacy
import Langlands.BaseChange.RegularSemisimpleOrbit
import Langlands.BaseChange.SigmaLiftCharacterIdentity.Parameters
import Langlands.TraceFormula.TwistedOrbitClosedEmbedding

/-! Closed regular twisted conjugacy orbits over a cyclic field extension. -/

noncomputable section

namespace Langlands.BaseChange

open Langlands.JacquetLanglands Langlands.TraceFormula _root_.Topology
open Langlands.HarmonicAnalysis.Distribution (conjAct_orbit_eq)

universe u v

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
  {n l : ℕ} {σ : E ≃ₐ[F] E} (hσ : IsCyclicAlgebra σ l) (δ : GeneralLinear n E)

include hσ

/-- Over a cyclic field extension, a twisted orbit is the inverse image of the ordinary
conjugacy orbit of its cyclic norm. -/
theorem range_twistedConj_eq_cyclicNorm_preimage_orbit :
    Set.range (fun x : GeneralLinear n E => twistedConj (entrywiseAut σ n) x δ) =
      cyclicNorm σ l ⁻¹' MulAction.orbit (ConjAct (GeneralLinear n E)) (cyclicNorm σ l δ) := by
  rw [conjAct_orbit_eq]
  ext d
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x⁻¹, ?_⟩
    change x⁻¹ * cyclicNorm σ l δ * x⁻¹⁻¹ =
      cyclicNorm σ l (x⁻¹ * δ * entrywiseAut σ n x)
    rw [cyclicNorm_twistedConj, hσ.pow_eq_one, entrywiseAut_one_apply, inv_inv]
  · rintro ⟨x, hx⟩
    obtain ⟨g, hg⟩ := twistedConj_of_cyclicNorm_conj_of_field hσ x⁻¹ (by simpa using hx)
    exact ⟨g, hg⟩

variable [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]
  [T2Space E]

/-- A cyclic twisted orbit of regular semisimple norm is closed. -/
theorem isClosed_range_twistedConj_of_regularNorm (hd : IsRegularSemisimple (cyclicNorm σ l δ)) :
    IsClosed (Set.range fun x : GeneralLinear n E => twistedConj (entrywiseAut σ n) x δ) := by
  rw [range_twistedConj_eq_cyclicNorm_preimage_orbit hσ]
  exact (isClosed_regularSemisimpleOrbit _ hd).preimage (SigmaLiftCharacterIdentity.continuous_cyclicNorm σ l)

variable [LocallyCompactSpace (GeneralLinear n E)] [SigmaCompactSpace (GeneralLinear n E)]

/-- A continuous compactly supported test function pulls back to a continuous
compactly supported function on the regular twisted centralizer quotient. -/
theorem continuous_hasCompactSupport_cyclicTwistedOrbitFunction (f : GeneralLinear n E → ℂ)
    (hd : IsRegularSemisimple (cyclicNorm σ l δ)) (hf : Continuous f) (hf₀ : HasCompactSupport f) :
    Continuous (twistedOrbitFunction (entrywiseAut σ n) δ f) ∧
      HasCompactSupport (twistedOrbitFunction (entrywiseAut σ n) δ f) := by
  have he := isClosedEmbedding_twistedOrbitFunction_id (entrywiseAut σ n)
    (SigmaLiftCharacterIdentity.continuous_entrywiseAut σ) δ
    (isClosed_range_twistedConj_of_regularNorm hσ δ hd)
  have hEq : twistedOrbitFunction (entrywiseAut σ n) δ f =
      f ∘ twistedOrbitFunction (entrywiseAut σ n) δ id := by
    funext q
    induction q using Quotient.inductionOn with
    | h g => rfl
  rw [hEq]
  exact ⟨hf.comp he.continuous, hf₀.comp_isClosedEmbedding he⟩

end Langlands.BaseChange
