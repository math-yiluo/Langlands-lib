import Langlands.Global.RankinSelberg.RealGodementSpanGrowth
import Langlands.Global.RankinSelberg.RealGodementSpanLie

/-! # Continued real Godement evaluation on the K-finite standard module -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open GramFormula PartialJacquet RealJacquetFrobenius

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

variable {t : ℕ}

local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "X" => Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ

/-- The K-finite standard module embeds into the compact Godement section span by
inclusion of its functions. -/
def compactSectionKFiniteInclusion (D : RealQuotientMeasureData t) (c : RealCharacterData)
    (ds : List RealBlock) :
    Automorphic.realStandardKFinite (t + 2) (.character c :: ds) →ₗ[ℂ] compactSectionSpan D.groupHaar c ds := by
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let : μ.IsMulRightInvariant := (realMatrixHaar_symmetries μ).1
  exact Submodule.inclusion fun F hF => realGodementFiniteGeneration (t + 1) μ c ds F ⟨hF.1.1, hF.2⟩

@[simp] theorem compactSectionKFiniteInclusion_val (D : RealQuotientMeasureData t)
    (c : RealCharacterData) (ds : List RealBlock)
    (F : Automorphic.realStandardKFinite (t + 2) (.character c :: ds)) :
    (compactSectionKFiniteInclusion D c ds F).val = F.val := rfl

/-- For dominant lower position exponents and any leading exponent, the compact
Godement evaluation restricts to a uniform upper Whittaker intertwiner. -/
def RealGodementUniformModelStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (a : ℝˣ) (p : Fin 2) (ds : List RealBlock),
    IsStrictlyDominant (realPositionExponent ds) t → ∀ w : ℂ,
    let c := charData p w
    let V := compactSectionSpan D.groupHaar c ds
    ∃ J : V →ₗ[ℂ] (H → ℂ),
      IsRealUniformWhittakerIntertwiner (t + 1) (.character c :: ds) (-a)
        (J.comp (compactSectionKFiniteInclusion D c ds)) ∧
      ∀ (f : principalSeries ℝ (t + 1) (realPositionCharacter ds))
        (S : Set X), IsCompact S → (∀ x ∈ S, HasFullRowRank x) →
        ∀ (Φ : 𝓢(X, ℂ)), (∀ x ∉ S, Φ x = 0) →
        ∀ F : V, F.val = sectionValue D.groupHaar c f.val Φ → ∀ g,
          J F g = godementLeadingFamily D a Φ (additiveJacquetIntegral a f.val) p g w

theorem realGodementUniformModel : RealGodementUniformModelStatement (t := t) := by
  intro D a p ds hDom w c V
  obtain ⟨J, hJ, hRight, hLeft⟩ := realGodementSpanEquivariance t D a p ds hDom w
  obtain ⟨hSmooth, hLie⟩ := realGodementSpanLie D a p ds hDom w J hJ
  obtain ⟨N, hN⟩ := realGodementSpanGrowth t D a p ds hDom w
  let ι := compactSectionKFiniteInclusion D c ds
  refine ⟨J, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, N, fun F => hN J hJ (ι F)⟩, hJ⟩
  · intro F u hu g
    exact hLeft (ι F) ⟨u, hu⟩ g
  · exact fun F => hSmooth (ι F)
  · intro F
    obtain ⟨C, _, hC⟩ := hN J hJ (ι F)
    exact ⟨C, N, hC⟩
  · intro k F F' hF
    have hEq : ι F' = compactSectionRightTranslation D.groupHaar c ds k.val (ι F) := Subtype.ext hF
    change J (ι F') = _
    rw [hEq]
    exact hRight k.val (ι F)
  · intro B F F' hF
    obtain ⟨T, hT⟩ := hLie B
    have hEq : ι F' = T (ι F) := Subtype.ext (hF.trans (hT (ι F)).1.symm)
    change J (ι F') = _
    rw [hEq]
    exact (hT (ι F)).2

end Langlands.Global.RankinSelbergGlobal.RealGodement
