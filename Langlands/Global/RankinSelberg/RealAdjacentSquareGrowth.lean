import Langlands.Global.RankinSelberg.RealAdjacentCompactProjection
import Langlands.Global.RankinSelberg.RealMatrixCoefficientGrowth
import Langlands.Global.RankinSelberg.RealLocalAdjacentUnfolding

/-! # The square factor of the real adjacent-rank expansion

See the paired Markdown file.
-/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap NNReal
open Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open ArchimedeanLocal
open Langlands.Archimedean (unitaryCompact realPositionCharacter realRank_map_character)
open RealGodement (realRectangularSchwartzFourier)

attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel

variable {r : ℕ}

local notation "H" => Langlands.GeneralLinear (r + 1) ℝ
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "ι" => GeneralLinear.inverseTranspose (r + 1) ℝ

/-- The real matrix zeta kernel of a determinant-twisted coefficient is the adjacent matrix
weight times the coefficient. -/
theorem realMatrixZetaKernel_detCharacter (c : RealCharacterData) (F : Mat → ℂ) (C : H → ℂ)
    (s : ℂ) (z : H) :
    GodementJacquet.realMatrixZetaKernel (r := r)
        (fun g => RealPrincipalSeries.realDetCharacter c g * C g) F s z =
      realAdjacentMatrixWeight c.character.toMonoidHom F s z * C z := by
  unfold GodementJacquet.realMatrixZetaKernel realAdjacentMatrixWeight detCharacter
  change F z.val * ((c.character (GeneralLinear.determinant z) : ℂ) * C z) *
      ArchimedeanLocal.detPower realNormalizedAbs z (s + (r : ℂ) / 2) =
    F z.val * (c.character (GeneralLinear.determinant z) : ℂ) *
      ArchimedeanLocal.detPower realNormalizedAbs z (s + (r : ℂ) / 2) * C z
  ring

/-- The dual kernel: the inverse transpose inverts the determinant character. -/
theorem realMatrixZetaKernel_detCharacter_inverseTranspose (c : RealCharacterData)
    (F : Mat → ℂ) (C : H → ℂ) (s : ℂ) (z : H) :
    GodementJacquet.realMatrixZetaKernel (r := r)
        ((fun g => RealPrincipalSeries.realDetCharacter c g * C g) ∘ ι) F s z =
      realAdjacentMatrixWeight c.inverse.character.toMonoidHom F s z * C (ι z) := by
  unfold GodementJacquet.realMatrixZetaKernel realAdjacentMatrixWeight detCharacter
  simp only [Function.comp_apply]
  rw [RealPrincipalSeries.realDetCharacter_inverseTranspose]
  change F z.val * ((c.character (GeneralLinear.determinant z) : ℂ)⁻¹ * C (ι z)) *
      ArchimedeanLocal.detPower realNormalizedAbs z (s + (r : ℂ) / 2) =
    F z.val * (((c.character (GeneralLinear.determinant z))⁻¹ : ℂˣ) : ℂ) *
      ArchimedeanLocal.detPower realNormalizedAbs z (s + (r : ℂ) / 2) * C (ι z)
  rw [Units.val_inv_eq_inv_val]
  ring

variable {K : Type} [Group K] [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

/-- The two square matrix integrals of a compact pairing of a standard vector of a character
list, twisted by a real character `c`, converge on a right half-plane and have an entire
normalization of strip growth for the pair `[c] × es` at the Fourier parameter `a`. -/
theorem realAdjacentSquareGrowth (D : RealQuotientMeasureData r) (iK : K →* H)
    (hiK : Continuous iK) (hmem : ∀ k, iK k ∈ unitaryCompact ℝ (r + 1)) (μK : Measure K)
    [IsFiniteMeasure μK] (w : K → ℂ) (hw : Continuous w) (a : ℝˣ) (c : RealCharacterData)
    (F : 𝓢(Mat, ℂ)) (fs : List RealCharacterData) (hfs : fs.length = r + 1)
    (f : Automorphic.realStandardKFinite (r + 1) (fs.map RealBlock.character)) :
    let C : H → ℂ := fun z => ∫ k, w k * (f : H → ℂ) (iK k * z) ∂μK
    (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (fun z => realAdjacentMatrixWeight c.character.toMonoidHom F s z * C z)
        D.groupHaar ∧
      Integrable (fun z => realAdjacentMatrixWeight c.inverse.character.toMonoidHom
        (realRectangularSchwartzFourier a F) s z * C (ι z)) D.groupHaar) ∧
    HasRealPairNormalizedGrowth [RealBlock.character c] (fs.map RealBlock.character)
      ([RealBlock.character c].map RealLocalJacquet.dualBlock)
      ((fs.map RealBlock.character).map RealLocalJacquet.dualBlock) a
      (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) 1
      (fun s => ∫ z, realAdjacentMatrixWeight c.character.toMonoidHom F s z * C z ∂D.groupHaar)
      (fun s => ∫ z, realAdjacentMatrixWeight c.inverse.character.toMonoidHom
        (realRectangularSchwartzFourier a F) s z * C (ι z) ∂D.groupHaar) := by
  intro C
  let es : List RealBlock := fs.map RealBlock.character
  have : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let κ : Measure (unitaryCompact ℝ (r + 1)) := Measure.haar
  have hes : realRank es = r + 1 := by rw [realRank_map_character, hfs]
  let ℓ := compactPairing r (realPositionCharacter (RealPrincipalSeries.expand es)) iK hiK μK w hw
  have hℓ := hasCompactDerivativeBound_compactPairing (r := r) (RealPrincipalSeries.expand es)
    iK hiK hmem μK w hw
  let f₀ := RealPrincipalSeries.expandedSmoothInclusion r es f
  have hC (g : H) : ℓ (RealPrincipalSeries.translate r (RealPrincipalSeries.expand es) g f₀) =
      C g := compactPairing_translate (r := r) es iK hiK μK w hw f g
  let F' : H → ℂ := fun g => RealPrincipalSeries.realDetCharacter c g * C g
  have hF' : (fun g => RealPrincipalSeries.realDetCharacter c g *
      ℓ (RealPrincipalSeries.translate r (RealPrincipalSeries.expand es) g f₀)) = F' := by
    funext g
    rw [hC]
  have hF : (GodementJacquet.realMatrixZeta D.groupHaar F' F) =
      fun s => ∫ z, realAdjacentMatrixWeight c.character.toMonoidHom F s z * C z ∂D.groupHaar := by
    funext s
    unfold GodementJacquet.realMatrixZeta
    exact integral_congr_ae (ae_of_all _ fun z => realMatrixZetaKernel_detCharacter c F C s z)
  have hT : (RealSquareFourier.matrixTransform a F : Mat → ℂ) =
      realRectangularSchwartzFourier a F :=
    funext (GodementJacquet.matrixTransform_eq_realRectangularSchwartzFourier a F)
  have hFd : (GodementJacquet.realMatrixZeta D.groupHaar (F' ∘ ι)
      (RealSquareFourier.matrixTransform a F)) =
      fun s => ∫ z, realAdjacentMatrixWeight c.inverse.character.toMonoidHom
        (realRectangularSchwartzFourier a F) s z * C (ι z) ∂D.groupHaar := by
    funext s
    unfold GodementJacquet.realMatrixZeta
    rw [hT]
    exact integral_congr_ae (ae_of_all _ fun z =>
      realMatrixZetaKernel_detCharacter_inverseTranspose c _ C s z)
  have hexp : RealPrincipalSeries.expand es = es := RealGodement.expand_map_character fs
  refine ⟨?_, ?_⟩
  · obtain ⟨σ, M, Md, hInt, -⟩ := GodementJacquet.realMatrixPairIdentity_expand (r := r)
      D.groupHaar κ es hes f₀ ℓ hℓ c F a
    refine ⟨σ, fun s hs => ?_⟩
    obtain ⟨h1, h2⟩ := hInt s hs
    rw [hF'] at h1 h2
    refine ⟨h1.congr (ae_of_all _ fun z => realMatrixZetaKernel_detCharacter c F C s z), ?_⟩
    rw [hT] at h2
    exact h2.congr (ae_of_all _ fun z =>
      realMatrixZetaKernel_detCharacter_inverseTranspose c _ C s z)
  · have key := GodementJacquet.realMatrixPairNormalizedGrowth (r := r) D.groupHaar κ es hes f₀
      ℓ hℓ c F a
    dsimp only at key
    rw [hF', hF, hFd] at key
    exact RealGodement.hasRealPairNormalizedGrowth_list_congr hexp key

end Langlands.Global.RankinSelbergGlobal.RealJacquet
