import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonCutoff
import Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof

/-!
# Support of model functions along the rank-one embedding

For `σ` smooth on `GL_(m+2)` over a p-adic field and a model function `W` of a
standard functional, `W(diag(det g, 1, …, 1))` vanishes unless `det g` lies in a
fixed additive lattice. Right translation by small `1 + x E₀₁` fixes `W` and
multiplies these values by `ψ(det g · x)`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uV

section Covariance

variable {F : Type uF} [Field F] [TopologicalSpace F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Right translation by `1 + x E₀₁` multiplies a model function on the embedded
`GL₁` by `ψ(det g · x)`. -/
theorem glModelFunction_rankOneEmbedding_mul_cutoffUnipotent
    (ψ : UnitaryAdditiveCharacter F) {m : ℕ}
    (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F) V)
    (ℓ : glFunctionals ψ (m + 1) σ) (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
    (g : Langlands.GeneralLinear (0 + 1) F) (x : F) :
    glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g * rankOneCutoffUnipotent m x) =
      ψ.complex (((Matrix.GeneralLinearGroup.det g : Fˣ) : F) * x) *
        glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g) := by
  rw [rankOneEmbedding_mul_cutoffUnipotent]
  have h := glModelFunction_equivariance ψ (m + 1) σ ℓ w
    ⟨rankOneCutoffUnipotent m (((Matrix.GeneralLinearGroup.det g : Fˣ) : F) * x),
      rankOneCutoffUnipotent_mem m _⟩ (rankOneEmbedding m g)
  rw [standardCharacter_rankOneCutoffUnipotent] at h
  exact h

end Covariance

/-- A model function on the embedded `GL₁` is supported where `det g` lies in one
additive lattice of the supplied topological data. -/
theorem exists_rankOneEmbedding_support {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData)
    (ψ : letI := T.topology; UnitaryAdditiveCharacter F.Carrier)
    {m : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) V) :
    letI := T.topology
    IsSmooth σ →
    ∀ (ℓ : glFunctionals ψ (m + 1) σ) (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule),
      ∃ a : ℤ, ∀ g : Langlands.GeneralLinear (0 + 1) F.Carrier,
        glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g) ≠ 0 →
          ((Matrix.GeneralLinearGroup.det g : F.Carrierˣ) : F.Carrier) ∈
            T.additiveLattice a := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hσ ℓ w
  obtain ⟨K, hK⟩ := glModel_isSmooth ψ (m + 1) σ hσ ℓ w
  have hopen : IsOpen (rankOneCutoffUnipotent (F := F.Carrier) m ⁻¹'
      (K : Set (Langlands.GeneralLinear (m + 1 + 1) F.Carrier))) :=
    K.isOpen.preimage (continuous_transvectionUnit _ _ (rankOneCutoff_index_ne m))
  have h0 : (0 : F.Carrier) ∈ rankOneCutoffUnipotent (F := F.Carrier) m ⁻¹'
      (K : Set (Langlands.GeneralLinear (m + 1 + 1) F.Carrier)) := by
    change rankOneCutoffUnipotent (F := F.Carrier) m 0 ∈ K
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
  have hψ : ψ.complex (((Matrix.GeneralLinearGroup.det g : F.Carrierˣ) : F.Carrier) * x) = 1 :=
    (mul_eq_right₀ hg).mp h1.symm
  rw [UnitaryAdditiveCharacter.complex_apply] at hψ
  exact Subtype.ext hψ

end Langlands.RankinSelberg
