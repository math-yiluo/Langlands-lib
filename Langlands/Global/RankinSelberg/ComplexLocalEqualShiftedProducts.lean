import Langlands.Global.RankinSelberg.ComplexLocalEqualProductConvergence
import Langlands.Global.RankinSelberg.ComplexLocalCompactProducts
import Langlands.Global.RankinSelberg.ComplexLocalAdjacentExpansionConvergence
import Langlands.Global.RankinSelberg.ComplexLocalAdjoiningShift

/-! # The equal-rank finite products in the adjoining-exponent chamber -/

noncomputable section

open MeasureTheory
open Langlands.Archimedean Langlands.GeneralLinear Langlands.GodementJacquet
open Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open scoped Langlands.Archimedean.ComplexDuality Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal
open ComplexGodement (shiftedCharacter shiftedCharacter_exponent)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "sm" => ((m : ℕ) : ℂ) / 2
local notation "pad" => padGL (R := ℂ) (Nat.le_succ m)
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs
local notation "gap" => Nat.lt_succ_self r

private theorem shifted_weightedMatrixTest (d : ComplexCharacterData) (Ψ : Mat → ℂ) (z t : ℂ) :
    complexWeightedMatrixTest (shiftedCharacter d z).character Ψ t =
      complexWeightedMatrixTest d.character Ψ (t + z) := by
  funext g
  change Ψ g.val * ((shiftedCharacter d z).character (determinant g) : ℂ) * P g t =
    Ψ g.val * (d.character (determinant g) : ℂ) * P g (t + z)
  rw [shiftedCharacter_det_apply, detPower_complex_add]
  ring

private theorem shifted_compactTranslate (d : ComplexCharacterData) (Ψ : Mat → ℂ) (z : ℂ)
    (k : K) (X : Mat) :
    complexCompactMatrixTranslate ((shiftedCharacter d z).character.toMonoidHom.comp invMonoidHom)
        Ψ k X =
      complexCompactMatrixTranslate (d.character.toMonoidHom.comp invMonoidHom) Ψ k X := by
  change ((shiftedCharacter d z).character ((determinant k.val)⁻¹) : ℂ) * Ψ ((k.val⁻¹).val * X) =
    (d.character ((determinant k.val)⁻¹) : ℂ) * Ψ ((k.val⁻¹).val * X)
  have h := shiftedCharacter_det_unitary d z k⁻¹
  simpa only [Subgroup.coe_inv, map_inv] using congrArg (fun y : ℂ => y * Ψ ((k.val⁻¹).val * X)) h

/-- The same unitary expansion works throughout the positive chamber.
Only the spectral variable of the matrix integrals receives the radial shift. -/
def ComplexLocalEqualShiftedProductsStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData (r + 1)) (D₁ : ComplexQuotientMeasureData r)
    (ν : Measure K) [IsFiniteMeasure ν] (i : K →* K), Continuous i →
  ∀ (κ : K → ℂ), Continuous κ →
  ∀ (a : ℂˣ) (d : ComplexCharacterData) (ds es : List ComplexCharacterData)
    (U : complexWhittakerModel r ds a) (V : complexWhittakerModel (r + 1) es (-a))
    (Ψ : 𝓢(Mat, ℂ)),
    (∀ X, ∫ k, κ k * complexCompactMatrixTranslate
      (d.character.toMonoidHom.comp invMonoidHom) Ψ (i k) X ∂ν = Ψ X) →
  ∀ (k : ℕ) (Vj bj : Fin k → G → ℂ) (Z : Fin k → ℂ → ℂ),
    (∀ j, Vj j ∈ complexWhittakerModel (r + 1) es (-a)) →
    (∀ x g, (∫ k, κ k * V.val (x * (i k).val * g) ∂ν) = ∑ j, Vj j x * bj j g) →
    (∃ β : ℝ, ∀ t : ℂ, β < t.re → ∀ j,
      let F := fun g => complexWeightedMatrixTest d.character Ψ (t + sm) g * bj j g
      Integrable F D.groupHaar ∧ Z j t = ∫ g, F g ∂D.groupHaar) →
    ∃ τ σ : ℝ, ∀ z s : ℂ, τ < z.re → σ < s.re →
      complexEqualUnfoldedIntegral D.groupHaar D₁ (shiftedCharacter d z).character Ψ U.val V.val s =
        ∑ j, complexUnequalIntegral gap D₁ (Vj j) U.val s * Z j (s + z)

set_option maxHeartbeats 1400000 in
theorem complexLocalEqualShiftedProducts : ComplexLocalEqualShiftedProductsStatement (r := r) := by
  intro D D₁ ν _ i hi κ hκ a d ds es U V Ψ hΨ k Vj bj Z hV hExp hZ
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : SigmaFinite D.groupHaar := complexLocalGroupHaarSigmaFinite D
  let : SigmaFinite D₁.measure := complexLocalQuotientSigmaFinite D₁
  obtain ⟨T, σ, hσ⟩ := complexLocalEqualProductConvergence D₁ D.groupHaar a ds es U V
  obtain ⟨ρ, hρ⟩ := complexLocalCompactInsertionIntegrability D.groupHaar ν i hi κ hκ d Ψ es (-a) V
  obtain ⟨β, hβ⟩ := hZ
  have hQ (j : Fin k) : ∃ σj : ℝ, ∀ s : ℂ, σj < s.re →
      Integrable (complexUnequalIntegrand gap (Vj j) U.val s) D₁.measure :=
    complexLocalOrdinaryConvergence gap es ds (-a) D₁ ⟨Vj j, hV j⟩
      ⟨U.val, by simpa only [neg_neg] using U.2⟩
  choose σj hσj using hQ
  obtain ⟨βQ, hβQ⟩ := (Set.finite_range σj).bddAbove
  let t₀ : ℝ := (m : ℝ) / 2
  have ht₀ : (sm).re = t₀ := by
    have ht : (t₀ : ℂ) = sm := by simp [t₀]
    rw [← ht, Complex.ofReal_re]
  refine ⟨max 0 (T - d.exponent.re), max σ (max (ρ - t₀) (max β βQ)), ?_⟩
  intro z s hz hs
  simp only [max_lt_iff] at hz hs
  obtain ⟨hz₀, hzT⟩ := hz
  obtain ⟨hs, hsρ, hsβ, hsQ⟩ := hs
  let d' := shiftedCharacter d z
  have hz' : T ≤ d'.exponent.re := by
    dsimp only [d']
    rw [shiftedCharacter_exponent, Complex.add_re]
    linarith
  have hQ' (j : Fin k) := hσj j s ((hβQ (Set.mem_range_self j)).trans_lt hsQ)
  have hzβ : β < (s + z).re := by rw [Complex.add_re]; linarith
  have hzρ : ρ < (s + sm + z).re := by rw [Complex.add_re, Complex.add_re, ht₀]; linarith
  have hShift (g : G) : complexWeightedMatrixTest d'.character Ψ (s + sm) g =
      complexWeightedMatrixTest d.character Ψ (s + z + sm) g := by
    dsimp only [d']
    rw [shifted_weightedMatrixTest, add_right_comm s]
  have hΨ' (X : Mat) : (∫ k, κ k * complexCompactMatrixTranslate
      (d'.character.toMonoidHom.comp invMonoidHom) Ψ (i k) X ∂ν) = Ψ X := by
    dsimp only [d']
    simp_rw [shifted_compactTranslate]
    exact hΨ X
  have hInt : ∀ᵐ q ∂D₁.measure, Integrable (fun p : K × G =>
      κ p.1 * complexWeightedMatrixTest d'.character Ψ (s + sm) ((i p.1).val⁻¹ * p.2) *
        complexEqualUnfoldedInner U.val V.val p.2 s q) (ν.prod D.groupHaar) := by
    refine ae_of_all _ fun q => ?_
    have h := (hρ (s + sm + z) hzρ (pad q.out)).mul_const (U.val q.out * P q.out (s - 1 / 2))
    refine h.congr (ae_of_all _ fun p => ?_)
    dsimp only
    rw [hShift, add_right_comm s z, complexEqualUnfoldedInner]
    ring
  have hMat (j : Fin k) : Integrable (fun g =>
      complexWeightedMatrixTest d'.character Ψ (s + sm) g * bj j g) D.groupHaar := by
    simp_rw [hShift]
    exact (hβ (s + z) hzβ j).1
  rw [complexEqualUnfoldedIntegral_eq_sum_products D.groupHaar D₁ ν i hi.measurable κ
    d'.character Ψ U.val V.val s hΨ' Vj bj hExp (hσ d' hz' Ψ s hs) hInt hQ' hMat]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [hShift]
  rw [(hβ (s + z) hzβ j).2]

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
