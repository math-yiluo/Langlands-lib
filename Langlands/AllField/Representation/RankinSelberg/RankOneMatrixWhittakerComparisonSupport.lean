import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonSupport
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonCutoff
/-!
# Support of model functions along the rank-one embedding

For `σ` smooth on `GL_(m+2)` over a p-adic field and a model function `W` of a
standard functional, `W(diag(det g, 1, …, 1))` vanishes unless `det g` lies in a
fixed additive lattice. Right translation by small `1 + x E₀₁` fixes `W` and
multiplies these values by `ψ(det g · x)`.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding LastRowCompactOrbitStatement ZeroRowLastRowCutoffStatement exists_rankOneCutoff exists_rankOneEmbedding_support lastRowCompactOrbit zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear

universe uF uV

section Covariance


end Covariance

/-- A model function on the embedded `GL₁` is supported where `det g` lies in one
additive lattice of the supplied topological data. -/
theorem exists_rankOneEmbedding_support {F : Type uF} [Field F]
    (T : LocalFieldData F)
    (ψ : letI := T.topology; UnitaryAdditiveCharacter F)
    {m : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F) V) :
    letI := T.topology
    IsSmooth σ →
    ∀ (ℓ : glFunctionals ψ (m + 1) σ) (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule),
      ∃ a : ℤ, ∀ g : Langlands.GeneralLinear (0 + 1) F,
        glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g) ≠ 0 →
          ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) ∈
            T.additiveLattice a := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hσ ℓ w
  obtain ⟨K, hK⟩ := glModel_isSmooth ψ (m + 1) σ hσ ℓ w
  have hopen : IsOpen (rankOneCutoffUnipotent (F := F) m ⁻¹'
      (K : Set (Langlands.GeneralLinear (m + 1 + 1) F))) :=
    K.isOpen.preimage (continuous_transvectionUnit _ _ (rankOneCutoff_index_ne m))
  have h0 : (0 : F) ∈ rankOneCutoffUnipotent (F := F) m ⁻¹'
      (K : Set (Langlands.GeneralLinear (m + 1 + 1) F)) := by
    change rankOneCutoffUnipotent (F := F) m 0 ∈ K
    rw [rankOneCutoffUnipotent, transvectionUnit_zero]
    exact K.one_mem
  obtain ⟨c, hc⟩ := T.exists_additiveLattice_subset (hopen.mem_nhds h0)
  refine ⟨T.additiveConductor ψ - c, fun g hg => ?_⟩
  apply T.mem_additiveLattice_of_forall_mul_eq_one ψ c
  intro x hx
  have hxK : rankOneCutoffUnipotent m x ∈ K := hc hx
  have hfix : glModelRepresentation ψ (m + 1) σ ℓ (rankOneCutoffUnipotent m x) w = w :=
    hK ⟨_, hxK⟩
  have h1 := glModelFunction_rankOneEmbedding_mul_cutoffUnipotent ψ σ ℓ w g x
  rw [← glModelFunction_translate, hfix] at h1
  have hψ : ψ.complex (((Matrix.GeneralLinearGroup.det g : Fˣ) : F) * x) = 1 :=
    (mul_eq_right₀ hg).mp h1.symm
  rw [UnitaryAdditiveCharacter.complex_apply] at hψ
  exact Subtype.ext hψ

end Langlands.AllField.RankinSelberg
