import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonCutoff
import Langlands.AllField.Group.GL.MirabolicTailConullProof
import Langlands.AllField.HarmonicAnalysis.PadicSelfDualMeasureExistsProof
import Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement
/-!
# Fourier cutoff along the rank-one embedding

For `σ` smooth on `GL_(m+2)`, a standard functional `ℓ`, a model function `W` of `ℓ`
and a Schwartz–Bruhat function `φ` on `F`, there is a model function `W'` of the
same `ℓ` with `W'(diag(det g, 1, …, 1)) = φ(det g) W(diag(det g, 1, …, 1))` for every
`g ∈ GL₁`. The function `W'` is the right smearing of `W` along `x ↦ 1 + x E₀₁`
against a Fourier preimage of `φ`.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding LastRowCompactOrbitStatement ZeroRowLastRowCutoffStatement exists_rankOneCutoff lastRowCompactOrbit zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear

universe uF uV

section Matrix


end Matrix

section Character


end Character

section Cutoff


end Cutoff

/-- The Fourier cutoff along `rankOneEmbedding m` for the canonical topology of a
p-adic field: every `φ(det g)` multiple of a model function on the embedded `GL₁` is
the restriction of a model function of the same functional. -/
theorem exists_rankOneCutoff (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    {m : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F) V) :
    IsSmooth σ →
    ∀ (ℓ : glFunctionals ψ (m + 1) σ) (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (φ : SchwartzBruhat F),
      ∃ w' : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule,
        ∀ g : Langlands.GeneralLinear (0 + 1) F,
          glModelFunction ψ (m + 1) σ ℓ w' (rankOneEmbedding m g) =
            φ ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) *
              glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g) := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  let := isUniformAddGroup_of_addCommGroup (G := F)
  let := borel F
  have : BorelSpace F := ⟨rfl⟩
  have : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
  intro hσ ℓ w φ
  obtain ⟨htd, hexists⟩ := padicSelfDualMeasureExists F (⟨⟩ : LocalFieldData F)
  obtain ⟨μ, hμ⟩ := hexists ψ
  exact exists_rankOneCutoff_of_isSelfDual ψ μ hμ σ hσ ℓ w φ

end Langlands.AllField.RankinSelberg
