import Langlands.Analysis.SchwartzMatrixNorm
import Langlands.Global.RankinSelberg.ComplexLocalCompactMatchedProjection
import Langlands.Global.RankinSelberg.ComplexLocalCompactFourierAveraging
import Langlands.Global.RankinSelberg.ComplexLocalMatrixEquation

/-! # Matched compact matrix factors for the complex Jacquet expansions -/

noncomputable section

open MeasureTheory
open Langlands.Analysis.SchwartzMatrixNorm
open Langlands.Archimedean Langlands.Archimedean.ComplexDuality Langlands.Automorphic
open Langlands.GodementJacquet Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Elementwise SchwartzMap Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel

variable {r : ℕ}

local notation "n" => r + 1
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "ι" => GeneralLinear.inverseTranspose n ℂ
local notation "wd" => ArchimedeanLocal.dualFunction n
local notation "μK" => unitaryHaar n

/-- The same Schwartz matrix test with the operator norm on its domain. -/
def complexMatrixEntryToOperator {m p : ℕ}
    (Φ : EntrySchwartz m p) : OperatorSchwartz m p :=
  @SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (Matrix (Fin m) (Fin p) ℂ) (Matrix (Fin m) (Fin p) ℂ) ℂ
    Matrix.normedAddCommGroup Matrix.normedSpace _ _ _
    Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace _
    (ContinuousLinearEquiv.refl ℝ (Matrix (Fin m) (Fin p) ℂ)) Φ

theorem coe_complexMatrixEntryToOperator {m p : ℕ} (Φ : EntrySchwartz m p) :
    (complexMatrixEntryToOperator Φ : Matrix (Fin m) (Fin p) ℂ → ℂ) = Φ := rfl

theorem inverseCharacter_hom (d : ComplexCharacterData) :
    (d.inv.character : ℂˣ →* ℂˣ) = (d.character : ℂˣ →* ℂˣ).comp invMonoidHom := by
  ext z
  change (d.inv.character z : ℂ) = (d.character z⁻¹ : ℂ)
  rw [d.inv_character_apply, map_inv, Units.val_inv_eq_inv_val]

private theorem positionCharacter_ofFn {m : ℕ} (e : Fin m → ComplexCharacterData)
    (i : Fin m) (z : ℂˣ) :
    complexPositionCharacter (List.ofFn e) i.val z = ((e i).character z : ℂ) := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    rw [List.ofFn_succ]
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih (fun k => e k.succ) j

private theorem matrixEquation_of_compactBorel [mK : MeasurableSpace K] [BorelSpace K]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure K) [ν.IsHaarMeasure] [SFinite ν]
    (d : ComplexCharacterData) (e : Fin n → ComplexCharacterData)
    (f : complexStandardKFinite n (List.ofFn e)) (κ : K → ℂ) (hκ : Continuous κ)
    (Φ : 𝓢(Mat, ℂ)) :
    let b (g : G) := ∫ k, κ k * (f : G → ℂ) (k.val * g) ∂ν
    ∃ (Z Zd : ℂ → ℂ), Meromorphic Z ∧ Meromorphic Zd ∧
      PairMeromorphicEquation [d] (List.ofFn e) 1 1 Z Zd ∧
      HasComplexPairNormalizedGrowth [d] (List.ofFn e) 1 1 Z Zd ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        Integrable (complexJacquetMatrixIntegrand d b Φ s) μ ∧
        Integrable (complexJacquetMatrixIntegrand d.inv (b ∘ ι) (complexMatrixFourier 1 Φ) s) μ ∧
        Z s = (∫ g, complexJacquetMatrixIntegrand d b Φ s g ∂μ) ∧
        Zd s = (∫ g, complexJacquetMatrixIntegrand d.inv (b ∘ ι) (complexMatrixFourier 1 Φ) s g ∂μ) := by
  have hK : mK = (Subtype.instMeasurableSpace : MeasurableSpace K) := by
    trans borel K
    · exact BorelSpace.measurable_eq
    · symm
      exact @BorelSpace.measurable_eq K _ Subtype.instMeasurableSpace (Subtype.borelSpace _)
  subst mK
  obtain ⟨Z, Zd, hZ, hZd, hFE, σ, hσ⟩ :=
    complexLocalMatrixEquation (r := r) μ ν d e (complexPositionCharacter (List.ofFn e))
      (positionCharacter_ofFn e) (f : G → ℂ) f.2.1 κ hκ Φ
  obtain ⟨A, Ad, hA, hAd, hAg, hAdg, ⟨τ, hτ⟩, hEq⟩ :=
    complexLocalMatrixGrowth (r := r) μ ν d e (complexPositionCharacter (List.ofFn e))
      (positionCharacter_ofFn e) (f : G → ℂ) f.2.1 κ hκ Φ
  refine ⟨Z, Zd, hZ, hZd, hFE, ?_, σ, hσ⟩
  refine ⟨A, Ad, hA, hAd, hAg, hAdg, ⟨max σ τ, ?_⟩, hEq⟩
  intro s hs
  obtain ⟨hP, hD⟩ := hτ s ((le_max_right _ _).trans_lt hs)
  obtain ⟨_, _, hp, hd⟩ := hσ s ((le_max_left _ _).trans_lt hs)
  exact ⟨hP.trans (congrArg (_ * ·) hp.symm), hD.trans (congrArg (_ * ·) hd.symm)⟩

/-- One continuous compact weight reproduces the two square tests and yields matching
finite expansions with the meromorphic matrix factors for the adjoining character. -/
def ComplexLocalMatchedMatrixGrowthStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure]
    (d : ComplexCharacterData) (e : Fin n → ComplexCharacterData) (a : ℂˣ)
    (B : complexStandardKFinite n (List.ofFn e) →ₗ[ℂ] (G → ℂ)),
    IsComplexWhittakerIntertwiner r (List.ofFn e) a B →
  ∀ (f : complexStandardKFinite n (List.ofFn e)) (Φ : 𝓢(Mat, ℂ)),
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun X => Φ ((k.val⁻¹).val * X))) →
    ∃ (κ : K → ℂ) (m : ℕ) (V : Fin m → G → ℂ) (b : Fin m → G → ℂ)
      (Z Zd : Fin m → ℂ → ℂ),
      Continuous κ ∧
      (∀ X, ∫ k, κ k * complexCompactMatrixTranslate
        ((d.character : ℂˣ →* ℂˣ).comp invMonoidHom) Φ k X ∂μK = Φ X) ∧
      (∀ X, ∫ k, κ k * complexCompactMatrixTranslate d.character (complexMatrixFourier 1 Φ)
        (complexUnitaryInverseTranspose n k) X ∂μK = complexMatrixFourier 1 Φ X) ∧
      (∀ x g : G,
        (∫ k, κ k * B f (x * k.val * g) ∂μK) = ∑ j, V j x * b j g ∧
        (∫ k, κ k * wd (B f) (x * ι k.val * g) ∂μK) = ∑ j, wd (V j) x * b j (ι g)) ∧
      (∀ j, V j ∈ complexWhittakerModel r (List.ofFn e) a ∧
        MeromorphicOn (Z j) Set.univ ∧ MeromorphicOn (Zd j) Set.univ ∧
        PairMeromorphicEquation [d] (List.ofFn e) 1 1 (Z j) (Zd j) ∧
        HasComplexPairNormalizedGrowth [d] (List.ofFn e) 1 1 (Z j) (Zd j)) ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ j,
        Integrable (complexJacquetMatrixIntegrand d (b j) Φ s) μ ∧
        Integrable (complexJacquetMatrixIntegrand d.inv (b j ∘ ι) (complexMatrixFourier 1 Φ) s) μ ∧
        Z j s = (∫ g, complexJacquetMatrixIntegrand d (b j) Φ s g ∂μ) ∧
        Zd j s = (∫ g, complexJacquetMatrixIntegrand d.inv (b j ∘ ι)
          (complexMatrixFourier 1 Φ) s g ∂μ)

theorem complexLocalMatchedMatrixGrowth : ComplexLocalMatchedMatrixGrowthStatement (r := r) := by
  intro μ _ d e a B hB f Φ hΦfin
  let η : ℂˣ →* ℂˣ := d.character
  have hη : Continuous η := d.character.continuous
  obtain ⟨κ, hκ, hκfin, hΦ⟩ := complexLocalCompactMatrixWeight μK inferInstance
    (η.comp invMonoidHom) (hη.comp continuous_inv) Φ Φ.continuous hΦfin
  have hΦInt : Integrable (Φ : Mat → ℂ)
      (RankinSelberg.rectangularMeasure (complexSelfDualMeasure 1) n n) := by
    let ν := complexSelfDualMeasure (1 : ℂˣ)
    let : ν.measure.IsAddHaarMeasure := ν.isAddHaar
    let : (RankinSelberg.rectangularMeasure ν n n).IsAddHaarMeasure :=
      RankinSelberg.rectangularMeasure_isAddHaar ν n n
    exact Φ.integrable
  have hΦd := complexLocalCompactFourierWeight 1 μK inferInstance κ hκ η hη Φ hΦInt hΦ
  obtain ⟨p, hp, hProj⟩ :=
    complexLocalCompactMatchedProjection (r := r) (List.ofFn e) a μK inferInstance κ hκ hκfin B hB f
  obtain ⟨m, V, κ', hV, hExp⟩ :=
    complexLocalCompactProjectionReduction (r := r) (List.ofFn e) a μK inferInstance κ hκ hκfin
      f B hB p hp hProj
  let b (j : Fin m) (g : G) := ∫ k, κ' j k * (f : G → ℂ) (k.val * g) ∂μK
  have hMatrix (j : Fin m) := matrixEquation_of_compactBorel μ μK d e f (κ' j) (hV j).2 Φ
  choose Z Zd hZ hZd hFE hGrowth σ hσ using hMatrix
  obtain ⟨τ, hτ⟩ := (Set.finite_range σ).bddAbove
  refine ⟨κ, m, V, b, Z, Zd, hκ, hΦ, hΦd, hExp, ?_, τ, ?_⟩
  · exact fun j => ⟨(hV j).1, fun s _ => hZ j s, fun s _ => hZd j s, hFE j, hGrowth j⟩
  · exact fun s hs j => hσ j s ((hτ (Set.mem_range_self j)).trans_lt hs)

/-- The finite compact expansion with its meromorphic matrix factors. -/
def ComplexLocalMatchedMatrixExpansionStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure]
    (d : ComplexCharacterData) (e : Fin n → ComplexCharacterData) (a : ℂˣ)
    (B : complexStandardKFinite n (List.ofFn e) →ₗ[ℂ] (G → ℂ)),
    IsComplexWhittakerIntertwiner r (List.ofFn e) a B →
  ∀ (f : complexStandardKFinite n (List.ofFn e)) (Φ : 𝓢(Mat, ℂ)),
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun X => Φ ((k.val⁻¹).val * X))) →
    ∃ (κ : K → ℂ) (m : ℕ) (V : Fin m → G → ℂ) (b : Fin m → G → ℂ)
      (Z Zd : Fin m → ℂ → ℂ),
      Continuous κ ∧
      (∀ X, ∫ k, κ k * complexCompactMatrixTranslate
        ((d.character : ℂˣ →* ℂˣ).comp invMonoidHom) Φ k X ∂μK = Φ X) ∧
      (∀ X, ∫ k, κ k * complexCompactMatrixTranslate d.character (complexMatrixFourier 1 Φ)
        (complexUnitaryInverseTranspose n k) X ∂μK = complexMatrixFourier 1 Φ X) ∧
      (∀ x g : G,
        (∫ k, κ k * B f (x * k.val * g) ∂μK) = ∑ j, V j x * b j g ∧
        (∫ k, κ k * wd (B f) (x * ι k.val * g) ∂μK) = ∑ j, wd (V j) x * b j (ι g)) ∧
      (∀ j, V j ∈ complexWhittakerModel r (List.ofFn e) a ∧
        MeromorphicOn (Z j) Set.univ ∧ MeromorphicOn (Zd j) Set.univ ∧
        PairMeromorphicEquation [d] (List.ofFn e) 1 1 (Z j) (Zd j)) ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ j,
        Integrable (complexJacquetMatrixIntegrand d (b j) Φ s) μ ∧
        Integrable (complexJacquetMatrixIntegrand d.inv (b j ∘ ι) (complexMatrixFourier 1 Φ) s) μ ∧
        Z j s = (∫ g, complexJacquetMatrixIntegrand d (b j) Φ s g ∂μ) ∧
        Zd j s = (∫ g, complexJacquetMatrixIntegrand d.inv (b j ∘ ι)
          (complexMatrixFourier 1 Φ) s g ∂μ)

theorem complexLocalMatchedMatrixExpansion :
    ComplexLocalMatchedMatrixExpansionStatement (r := r) := by
  intro μ _ d e a B hB f Φ hΦfin
  obtain ⟨κ, k, V, b, Z, Zd, hκ, hΦ, hΦd, hExp, hJ, τ, hτ⟩ :=
    complexLocalMatchedMatrixGrowth μ d e a B hB f Φ hΦfin
  exact ⟨κ, k, V, b, Z, Zd, hκ, hΦ, hΦd, hExp,
    fun j => ⟨(hJ j).1, (hJ j).2.1, (hJ j).2.2.1, (hJ j).2.2.2.1⟩, τ, hτ⟩

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
