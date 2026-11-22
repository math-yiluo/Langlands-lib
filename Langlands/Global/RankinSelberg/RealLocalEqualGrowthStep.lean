import Langlands.Global.RankinSelberg.RealLocalEqualCanonicalGrowth
import Langlands.Global.RankinSelberg.RealLocalCharacterGrowthInterfaces
import Langlands.Representation.Archimedean.RealCharacterCrossing
import Langlands.Global.RankinSelberg.ArchimedeanQuotientMeasures

/-! # The real equal-rank successor step with strip growth -/

noncomputable section

open MeasureTheory Set
open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped NNReal SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open ArchimedeanLocal
open Langlands.Archimedean.RealJacquetFrobenius (charData)

attribute [local instance 100] LieRing.ofAssociativeRing

private local instance (n : ℕ) (ds : List RealBlock) :
    NormedAddCommGroup (RealStandardCompactBanach.Carrier n ds) :=
  (RealStandardCompactBanach.closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) :
    NormedSpace ℂ (RealStandardCompactBanach.Carrier n ds) :=
  (RealStandardCompactBanach.closureSubmodule (n := n) ds).normedSpace

/-- Open premise: the uniform Whittaker model of a real character list, for the character
`-a`, lies in the range of the canonical Jacquet map with parameter `a`. -/
def RealUniformCanonicalRangePremise : Prop :=
  ∀ (r : ℕ) (a : ℝˣ) (p : Fin (r + 1) → Fin 2) (z : Fin (r + 1) → ℂ),
    realUniformWhittakerModel r (RealGodementProfiles.characterList p z) (-a) ≤
      LinearMap.range (canonicalJacquetMap a p z)

/-- Open premise: every canonical Jacquet map has a continuous Whittaker evaluation on the
smooth standard representation. -/
def RealCanonicalStandardEvaluationPremise : Prop :=
  ∀ (r : ℕ) (a : ℝˣ) (p : Fin (r + 1) → Fin 2) (z : Fin (r + 1) → ℂ),
    ∃ L : DerivativeSmoothVectors (matrixModel ℝ (r + 1))
        (RealStandardCompactBanach.representation (n := r + 1)
          (RealGodementProfiles.characterList p z)) →L[ℂ] ℂ,
      RealStandardCompactBanach.IsWhittakerStandardEvaluation
        (RealGodementProfiles.characterList p z) (-a) (canonicalJacquetMap a p z) L

/-- Open premise at one rank: the matrix normalized equation for orthogonal-finite square
tests, for the leading sign character `charData e 0` against a real character list of length
`t + 2`, with parameter `-a`, scale `√|a|` and sign `1`. -/
def RealMatrixCoefficientGrowthPremise (t : ℕ) : Prop :=
  ∀ (D' : RealQuotientMeasureData (t + 1)) (a : ℝˣ) (e : Fin 2) (fs : List RealCharacterData),
    fs.length = t + 2 →
  ∀ (f : Automorphic.realStandardKFinite (t + 2) (fs.map RealBlock.character))
    (Ψ : 𝓢(Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ, ℂ)),
    FiniteDimensional ℂ (Submodule.span ℂ (range fun k : unitaryCompact ℝ (t + 2) =>
      fun X' : Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ => Ψ (k.val⁻¹.val * X'))) →
    RealMatrixCoefficientNormalizedGrowth t D' a e (fs.map RealBlock.character) f Ψ
      [RealBlock.character (charData e 0)] (fs.map RealBlock.character)
      ([RealBlock.character (charData e 0)].map RealLocalJacquet.dualBlock)
      ((fs.map RealBlock.character).map RealLocalJacquet.dualBlock) (-a)
      (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) 1

/-- Every list of real character data of length `n` is a canonical character list. -/
theorem exists_characterList_eq {n : ℕ} (cs : List RealCharacterData) (hcs : cs.length = n) :
    ∃ (p : Fin n → Fin 2) (z : Fin n → ℂ),
      RealGodementProfiles.characterList p z = cs.map RealBlock.character := by
  subst hcs
  refine ⟨fun i => (cs.get i).parity, fun i => (cs.get i).exponent, ?_⟩
  simp only [RealGodementProfiles.characterList]
  congr 1
  conv_rhs => rw [← List.ofFn_get cs]
  congr 1
  funext i
  exact RealCharacterCrossing.charData_eta (cs.get i)

/-- The normalized property is unchanged when the parameter `-(-a)` and the scale
`√|-a|` are written as `a` and `√|a|`. -/
theorem hasRealPairNormalizedGrowth_neg_neg {xs ys xsd ysd : List RealBlock} {a : ℝˣ}
    {sign : ℂ} {Z Zd : ℂ → ℂ}
    (h : RealJacquet.HasRealPairNormalizedGrowth xs ys xsd ysd (-(-a))
      (NNReal.sqrt ‖((-a : ℝˣ) : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (-a).ne_zero))
      sign Z Zd) :
    RealJacquet.HasRealPairNormalizedGrowth xs ys xsd ysd a (NNReal.sqrt ‖(a : ℝ)‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) sign Z Zd := by
  have h1 : ‖((-a : ℝˣ) : ℝ)‖₊ = ‖(a : ℝ)‖₊ := by rw [Units.val_neg, nnnorm_neg]
  have key : ∀ (b : ℝˣ) (c : ℝ≥0) (hc : 0 < c), b = a → c = NNReal.sqrt ‖(a : ℝ)‖₊ →
      RealJacquet.HasRealPairNormalizedGrowth xs ys xsd ysd b c hc sign Z Zd →
      RealJacquet.HasRealPairNormalizedGrowth xs ys xsd ysd a (NNReal.sqrt ‖(a : ℝ)‖₊)
        (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) sign Z Zd := by
    rintro b c hc rfl rfl h
    exact h
  exact key _ _ _ (neg_neg a) (by rw [h1]) h

variable (t : ℕ) in
/-- The equal-rank successor: under the canonical range, canonical evaluation and matrix
premises, adjacent character growth at rank `t` gives equal character growth at rank `t + 1`. -/
def RealLocalEqualGrowthStepStatement : Prop :=
  RealUniformCanonicalRangePremise → RealCanonicalStandardEvaluationPremise →
    RealMatrixCoefficientGrowthPremise t →
    RealJacquet.RealLocalAdjacentCharacterGrowthAtRank t →
    RealJacquet.RealLocalEqualCharacterGrowthAtRank (t + 1)

theorem realLocalEqualGrowthStep (t : ℕ) : RealLocalEqualGrowthStepStatement t := by
  intro hRange hEval hMat hAdj ds es hds hes hrd hre a D W W' Φ hW hW'
  obtain ⟨cs, rfl⟩ := hds
  obtain ⟨fs₀, rfl⟩ := hes
  have hcs : cs.length = t + 2 := by rw [← Langlands.Archimedean.realRank_map_character]; exact hrd
  have hfs₀ : fs₀.length = t + 2 := by rw [← Langlands.Archimedean.realRank_map_character]; exact hre
  obtain ⟨P, Zs, hPZ⟩ := exists_characterList_eq cs hcs
  obtain ⟨P', Zs', hPZ'⟩ := exists_characterList_eq fs₀ hfs₀
  rw [← hPZ] at hW ⊢
  rw [← hPZ'] at hW' ⊢
  obtain ⟨F, rfl⟩ := hRange (t + 1) (-a) P Zs (by rwa [neg_neg])
  obtain ⟨F', rfl⟩ := hRange (t + 1) a P' Zs' hW'
  let fs : List RealCharacterData := List.ofFn fun i => charData (P' i) (Zs' i)
  have hfs : fs.length = t + 2 := List.length_ofFn
  have hB := realGodementCanonicalModel (t + 1) a P' Zs'
  obtain ⟨L, hL⟩ := hEval (t + 1) a P' Zs'
  let tail : List RealCharacterData :=
    List.ofFn fun i : Fin (t + 1) => charData (P i.succ) (Zs i.succ)
  have hAdj' : ∀ U ∈ realUniformWhittakerModel t (tail.map RealBlock.character) a,
      ∀ V ∈ realUniformWhittakerModel (t + 1) (fs.map RealBlock.character) (-a),
      RealJacquet.HasRealPairNormalizedGrowth (fs.map RealBlock.character)
        (tail.map RealBlock.character)
        ((fs.map RealBlock.character).map RealLocalJacquet.dualBlock)
        ((tail.map RealBlock.character).map RealLocalJacquet.dualBlock) a
        (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
        ((RealJacquet.determinant (fs.map RealBlock.character) (-1) : ℂ) ^ (t + 1) *
          (RealJacquet.determinant (tail.map RealBlock.character) (-1) : ℂ))
        (realUnequalIntegral (Nat.lt_succ_self t) (realQuotientMeasureData t) V U)
        (realUnequalDualIntegral (Nat.lt_succ_self t) (-a) (realQuotientMeasureData t) V U) := by
    intro U hU V hV
    exact hasRealPairNormalizedGrowth_neg_neg
      (hAdj (fs.map RealBlock.character) (tail.map RealBlock.character) ⟨fs, rfl⟩ ⟨tail, rfl⟩
        (by rw [Langlands.Archimedean.realRank_map_character, hfs]) (by rw [Langlands.Archimedean.realRank_map_character, List.length_ofFn])
        (-a) (realQuotientMeasureData t) V U hV (by rwa [neg_neg]))
  exact realLocalEqualCanonicalGrowth (realQuotientMeasureData t) D a P Zs fs hfs F
    (canonicalJacquetMap a P' Zs') hB ⟨L, hL⟩ F' Φ hAdj' (hMat D a (P 0) fs hfs F')

/-- The positive equal continuation target, reduced to the open premises: uniform
principal-series inclusion, canonical range, canonical evaluation, the matrix normalized
equation at every rank and adjacent character growth at every rank. -/
def RealLocalUniformPositiveEqualContinuationPremisesStatement : Prop :=
  RealUniformPrincipalSeriesInclusionStatement → RealUniformCanonicalRangePremise →
    RealCanonicalStandardEvaluationPremise → (∀ t : ℕ, RealMatrixCoefficientGrowthPremise t) →
    (∀ t : ℕ, RealJacquet.RealLocalAdjacentCharacterGrowthAtRank t) →
    RealLocalUniformPositiveEqualContinuationStatement

theorem realLocalUniformPositiveEqualContinuation_of_premises :
    RealLocalUniformPositiveEqualContinuationPremisesStatement := by
  intro hI hRange hEval hMat hAdj
  refine RealJacquet.realLocalUniformPositiveEqualContinuation_of_characterGrowth hI ?_
  intro r hr
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 1 := ⟨r - 1, by omega⟩
  exact realLocalEqualGrowthStep t hRange hEval (hMat t) (hAdj t)

end Langlands.Global.RankinSelbergGlobal.RealGodement
