import Langlands.Global.RankinSelberg.RealGodementUniformModel
import Langlands.Global.RankinSelberg.RealUniformWhittakerDual

/-! # Paired real Godement columns for continued upper coefficients and their duals -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Analysis.SchwartzCompactFamilies
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open GramFormula PartialJacquet RealJacquetFrobenius
open RealUniformWhittakerDual

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

/-- The pair of a coefficient and its reflected upper coefficient. -/
def reflectedCoefficientPair : (H → ℂ) →ₗ[ℂ] ((H → ℂ) × (H → ℂ)) where
  toFun W := (W, ArchimedeanLocal.dualFunction (t + 2) W)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The generator pairs obtained from a compact full-row-rank test and a uniform
lower coefficient with its reflected member in the reversed inverse model. -/
def compactReflectedColumnGenerators (D : RealQuotientMeasureData t) (a : ℝˣ)
    (cs : List RealCharacterData) (p : Fin 2) (w : ℂ) : Set ((H → ℂ) × (H → ℂ)) :=
  {Q | ∃ (W : G → ℂ) (S : Set X) (Φ : 𝓢(X, ℂ)),
    W ∈ realUniformWhittakerModel t (cs.map RealBlock.character) (-a) ∧
    ArchimedeanLocal.dualFunction (t + 1) W ∈ realUniformWhittakerModel t (dualCharacterBlocks cs) a ∧
    IsCompact S ∧ (∀ x ∈ S, HasFullRowRank x) ∧ (∀ x ∉ S, Φ x = 0) ∧
    Q = (fun g => godementLeadingFamily D a Φ W p g w,
      (((-1 : ℂ) ^ p.val) ^ (t + 1)) • fun g => godementLeadingFamily D (-a)
        (realRectangularSchwartzFourier a Φ) (ArchimedeanLocal.dualFunction (t + 1) W) p g (-w))}

/-- With a dominant lower character list, the continued upper coefficient and its
actual dual lie together in the linear span of the same reflected column generators. -/
def RealGodementReflectedPairsStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (a : ℝˣ) (cs : List RealCharacterData),
    cs.length = t + 1 →
    let ds := cs.map RealBlock.character
    IsStrictlyDominant (realPositionExponent ds) t → ∀ (p : Fin 2) (w : ℂ),
    let c := charData p w
    let V := compactSectionSpan D.groupHaar c ds
    ∃ J : V →ₗ[ℂ] (H → ℂ),
      let B := J.comp (compactSectionKFiniteInclusion D c ds)
      IsRealUniformWhittakerIntertwiner (t + 1) (.character c :: ds) (-a) B ∧
      (∀ (f : principalSeries ℝ (t + 1) (realPositionCharacter ds))
        (S : Set X), IsCompact S → (∀ x ∈ S, HasFullRowRank x) →
        ∀ (Φ : 𝓢(X, ℂ)), (∀ x ∉ S, Φ x = 0) →
        ∀ F : V, F.val = sectionValue D.groupHaar c f.val Φ → ∀ g,
          J F g = godementLeadingFamily D a Φ (additiveJacquetIntegral a f.val) p g w) ∧
      ∀ F, reflectedCoefficientPair (B F) ∈ Submodule.span ℂ (compactReflectedColumnGenerators D a cs p w)

theorem realGodementReflectedPairs : RealGodementReflectedPairsStatement (t := t) := by
  intro D a cs hLen ds hDom p w c V
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let : μ.IsMulRightInvariant := (realMatrixHaar_symmetries μ).1
  obtain ⟨J, hUniform, hGen⟩ := realGodementUniformModel D a p ds hDom w
  let V₀ := compactKFiniteLowerSectionSpan μ c ds
  let i := Submodule.inclusion (compactKFiniteLowerSectionSpan_le μ c ds)
  let P := reflectedCoefficientPair.comp (J.comp i)
  let Q := Submodule.span ℂ (compactReflectedColumnGenerators D a cs p w)
  let E : Set (H → ℂ) := {U | ∃ (f : G → ℂ) (S : Set X) (φ : X → ℂ),
    f ∈ kFiniteFunctions (principalSeries ℝ (t + 1) (realPositionCharacter ds)) (unitaryCompact ℝ (t + 1)) ∧
      IsCompact S ∧ (∀ x ∈ S, HasFullRowRank x) ∧ ContDiff ℝ ∞ φ ∧ (∀ x ∉ S, φ x = 0) ∧
      U = sectionValue μ c f φ}
  let A : Set V₀ := (Subtype.val : V₀ → H → ℂ) ⁻¹' E
  have hSpan : Submodule.span ℂ A = ⊤ := Submodule.span_span_coe_preimage
  have hLe : Submodule.span ℂ A ≤ Q.comap P := by
    apply Submodule.span_le.mpr
    intro U hU
    obtain ⟨f, S, φ, hf, hS, hRank, hφ, hZero, he⟩ := hU
    let Φ := ofCompactSupport φ hφ S hS hZero
    let W := additiveJacquetIntegral a f
    have hf' : f ∈ Automorphic.realStandardKFinite (t + 1) ds := by
      rw [show ds = cs.map RealBlock.character from rfl, standardKFinite_map_character]
      exact hf
    have hW : W ∈ realUniformWhittakerModel t ds (-a) :=
      realGodementOpenCellModel t ds a hDom ⟨f, hf'⟩
    have hWd : ArchimedeanLocal.dualFunction (t + 1) W ∈ realUniformWhittakerModel t (dualCharacterBlocks cs) a := by
      simpa only [neg_neg] using realUniformWhittakerCharacterDual t cs hLen (-a) W hW
    have hJ := funext (hGen ⟨f, hf.1⟩ S hS hRank Φ hZero (i U) he)
    change P U ∈ Q
    apply Submodule.subset_span
    refine ⟨W, S, Φ, hW, hWd, hS, hRank, hZero, ?_⟩
    change (J (i U), ArchimedeanLocal.dualFunction (t + 2) (J (i U))) = _
    rw [hJ]
    congr 1
    funext g
    exact godementLeadingFamily_reflection D a Φ hW hWd p g w
  refine ⟨J, hUniform, hGen, fun F => ?_⟩
  have hF : F.val ∈ V₀ := realGodementFiniteGenerationKFiniteLower (t + 1) μ c ds F.val
    ⟨F.property.1.1, F.property.2⟩
  have hQ : (⟨F.val, hF⟩ : V₀) ∈ Q.comap P := hLe (hSpan.symm ▸ Submodule.mem_top)
  exact hQ

/-- With a dominant lower character list, the continued upper coefficient and its
actual dual lie together in the linear span of the same reflected column generators. -/
def RealGodementReflectedIntertwinerStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (a : ℝˣ) (cs : List RealCharacterData),
    cs.length = t + 1 →
    let ds := cs.map RealBlock.character
    IsStrictlyDominant (realPositionExponent ds) t → ∀ (p : Fin 2) (w : ℂ),
    let es := .character (charData p w) :: ds
    ∃ B : Automorphic.realStandardKFinite (t + 2) es →ₗ[ℂ] (H → ℂ),
      IsRealUniformWhittakerIntertwiner (t + 1) es (-a) B ∧
      ∀ F, reflectedCoefficientPair (B F) ∈ Submodule.span ℂ (compactReflectedColumnGenerators D a cs p w)

theorem realGodementReflectedIntertwiner : RealGodementReflectedIntertwinerStatement (t := t) := by
  intro D a cs hLen ds hDom p w es
  let c := charData p w
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let : μ.IsMulRightInvariant := (realMatrixHaar_symmetries μ).1
  obtain ⟨J, hUniform, hGen⟩ := realGodementUniformModel D a p ds hDom w
  let V₀ := compactKFiniteLowerSectionSpan μ c ds
  let i := Submodule.inclusion (compactKFiniteLowerSectionSpan_le μ c ds)
  let P := reflectedCoefficientPair.comp (J.comp i)
  let Q := Submodule.span ℂ (compactReflectedColumnGenerators D a cs p w)
  let E : Set (H → ℂ) := {U | ∃ (f : G → ℂ) (S : Set X) (φ : X → ℂ),
    f ∈ kFiniteFunctions (principalSeries ℝ (t + 1) (realPositionCharacter ds)) (unitaryCompact ℝ (t + 1)) ∧
      IsCompact S ∧ (∀ x ∈ S, HasFullRowRank x) ∧ ContDiff ℝ ∞ φ ∧ (∀ x ∉ S, φ x = 0) ∧
      U = sectionValue μ c f φ}
  let A : Set V₀ := (Subtype.val : V₀ → H → ℂ) ⁻¹' E
  have hSpan : Submodule.span ℂ A = ⊤ := Submodule.span_span_coe_preimage
  have hLe : Submodule.span ℂ A ≤ Q.comap P := by
    apply Submodule.span_le.mpr
    intro U hU
    obtain ⟨f, S, φ, hf, hS, hRank, hφ, hZero, he⟩ := hU
    let Φ := ofCompactSupport φ hφ S hS hZero
    let W := additiveJacquetIntegral a f
    have hf' : f ∈ Automorphic.realStandardKFinite (t + 1) ds := by
      rw [show ds = cs.map RealBlock.character from rfl, standardKFinite_map_character]
      exact hf
    have hW : W ∈ realUniformWhittakerModel t ds (-a) :=
      realGodementOpenCellModel t ds a hDom ⟨f, hf'⟩
    have hWd : ArchimedeanLocal.dualFunction (t + 1) W ∈ realUniformWhittakerModel t (dualCharacterBlocks cs) a := by
      simpa only [neg_neg] using realUniformWhittakerCharacterDual t cs hLen (-a) W hW
    have hJ := funext (hGen ⟨f, hf.1⟩ S hS hRank Φ hZero (i U) he)
    change P U ∈ Q
    apply Submodule.subset_span
    refine ⟨W, S, Φ, hW, hWd, hS, hRank, hZero, ?_⟩
    change (J (i U), ArchimedeanLocal.dualFunction (t + 2) (J (i U))) = _
    rw [hJ]
    congr 1
    funext g
    exact godementLeadingFamily_reflection D a Φ hW hWd p g w
  refine ⟨J.comp (compactSectionKFiniteInclusion D c ds), hUniform, fun F => ?_⟩
  have hF : F.val ∈ V₀ := realGodementFiniteGenerationKFiniteLower (t + 1) μ c ds F.val
    ⟨F.property.1.1, F.property.2⟩
  have hQ : (⟨F.val, hF⟩ : V₀) ∈ Q.comap P := hLe (hSpan.symm ▸ Submodule.mem_top)
  exact hQ

end Langlands.Global.RankinSelbergGlobal.RealGodement
