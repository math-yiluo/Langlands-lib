import Langlands.Global.RankinSelberg.RealPairStripReflection
import Langlands.Global.RankinSelberg.RealUnequalCanonicalFamily

/-! # Continuing the real normalized unequal-rank equation in the larger exponents -/

noncomputable section

open Metric
open scoped NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealUnequalFamily

open ArchimedeanLocal RealEqualConvergence
open Langlands.LocalFactor.Archimedean
open Langlands.Archimedean (characterOfParams characterOfParams_eta)
open Langlands.Archimedean.RealJacquetFrobenius (charData)
open RealLocalWhittaker (iteratedRightDerivative regularFunctions)
open RealGodementProfiles (characterList IsCompactProfile standardSection standardSection_mem
  compactRestriction isCompactProfile_compactRestriction)
open RealBlockParameters (Shape blockOfParams blockList realPairStripReflection
  realCharacterData_ext)
open RealJacquet (HasRealPairNormalizedGrowth)

variable {r t : ℕ}
local notation "GT" => Langlands.GeneralLinear (t + 1) ℝ

/-- The discrete datum of a real block. -/
def blockShape : RealBlock → Shape
  | .character d => .inl d.parity
  | .induced d => .inr d.weight

/-- The complex exponent of a real block. -/
def blockExponent : RealBlock → ℂ
  | .character d => d.exponent
  | .induced d => d.exponent

theorem blockOfParams_shape_exponent (d : RealBlock) :
    blockOfParams (blockShape d) (blockExponent d) = d := by
  cases d with
  | character d =>
    exact congrArg RealBlock.character (realCharacterData_ext rfl rfl)
  | induced d =>
    exact congrArg RealBlock.induced (characterOfParams_eta d)

/-- Every real block list is a parametrized block list with constant exponents. -/
theorem eq_blockList (es : List RealBlock) :
    es = blockList (fun i : Fin es.length => blockShape es[i])
      (fun i : Fin es.length => blockExponent es[i]) := by
  unfold blockList
  simp only [blockOfParams_shape_exponent]
  exact (List.ofFn_getElem).symm

/-- A real character list is the parametrized block list with character shapes. -/
theorem characterList_eq_blockList {n : ℕ} (pr : Fin n → Fin 2) (z : Fin n → ℂ) :
    characterList pr z = blockList (fun i => .inl (pr i)) z := by
  unfold characterList blockList
  rw [List.map_ofFn]
  rfl

/-- The normalized pair with exponential strip growth for every larger canonical value at one
inducing parameter and a fixed smaller function. The canonical map for `-a` has left
character `a`; `b` is the dual measure parameter and `eb` the epsilon parameter. -/
def HasRealUnequalCanonicalPairGrowth (h : t < r) (a b eb : ℝˣ) (D : RealQuotientMeasureData t)
    (pr : Fin (r + 1) → Fin 2) (z : Fin (r + 1) → ℂ) (es : List RealBlock) (c : ℝ≥0)
    (hc : 0 < c) (sign : ℂ) (V : GT → ℂ) : Prop :=
  ∀ f : Automorphic.realStandardKFinite (r + 1) (characterList pr z),
    let W := RealGodement.canonicalJacquetMap (-a) pr z f
    HasRealPairNormalizedGrowth (characterList pr z) es
      ((characterList pr z).map RealLocalJacquet.dualBlock)
      (es.map RealLocalJacquet.dualBlock) eb c hc sign
      (realUnequalIntegral h D W V) (realUnequalDualIntegral h b D W V)

/-- The growth-preserving continuation of the real unequal-rank normalized equation along a
holomorphic family of larger inducing exponents, from a small disk about zero to parameter one,
for a fixed regular smaller function with polynomial derivative growth. -/
def RealUnequalCanonicalGrowthReflectionStatement : Prop :=
  ∀ (h : t < r) (a b eb : ℝˣ) (D : RealQuotientMeasureData t) (pr : Fin (r + 1) → Fin 2)
    (es : List RealBlock) (c : ℝ≥0) (hc : 0 < c) (sign : ℂ), sign ≠ 0 →
    ∀ V : GT → ℂ, (∀ Xs, iteratedRightDerivative t Xs V ∈ regularFunctions t (-a)) →
    (∃ N : ℕ, ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖iteratedRightDerivative t Xs V g‖ ≤ C * realMatrixHeight g ^ N) →
    ∀ (p : ℂ → Fin (r + 1) → ℂ), Differentiable ℂ p →
      (∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball 0 δ,
        HasRealUnequalCanonicalPairGrowth h a b eb D pr (p z) es c hc sign V) →
      HasRealUnequalCanonicalPairGrowth h a b eb D pr (p 1) es c hc sign V

theorem realUnequalCanonicalGrowthReflection :
    RealUnequalCanonicalGrowthReflectionStatement (r := r) (t := t) := by
  intro h a b eb D pr es c hc sign hsign V hregV hgrowthV p hp ⟨δ, hδ, hInit⟩ f
  let φ := compactRestriction f.val
  have hφ : IsCompactProfile pr φ := isCompactProfile_compactRestriction f.property
  let F := RealGodement.canonicalJacquetFamily (-a) hφ
  have hJ := RealGodement.canonicalJacquetFamily_properties (-a) hφ
  have hreg (z : Fin (r + 1) → ℂ) (Xs) :
      iteratedRightDerivative r Xs (F z) ∈ regularFunctions r a := by
    simpa only [neg_neg] using hJ.1 z Xs
  obtain ⟨σ, _, hZ, hZd, hBound⟩ := realUnequalRegularFamilyBounds h a b D (r + 1) F hreg
    hJ.2.1 (fun g => hJ.2.2.1 [] g) p hp V hregV hgrowthV 3
  let Z (u : ℂ × ℂ) := realUnequalIntegral h D (F (p u.1)) V u.2
  let Zd (u : ℂ × ℂ) := realUnequalDualIntegral h b D (F (p u.1)) V u.2
  let sh : Fin (r + 1) → Shape := fun i => .inl (pr i)
  let sh' := fun i : Fin es.length => blockShape es[i]
  let q := fun i : Fin es.length => blockExponent es[i]
  have hes : es = blockList sh' q := eq_blockList es
  have hInit' : ∀ z ∈ ball (0 : ℂ) δ,
      HasRealPairNormalizedGrowth (blockList sh (p z)) (blockList sh' ((fun _ => q) z))
        ((blockList sh (p z)).map RealLocalJacquet.dualBlock)
        ((blockList sh' ((fun _ => q) z)).map RealLocalJacquet.dualBlock) eb c hc sign
        (fun s => Z (z, s)) (fun s => Zd (z, s)) := by
    intro z hz
    have H := hInit z hz ⟨standardSection (p z) φ, standardSection_mem hφ (p z)⟩
    rw [RealGodement.canonicalJacquetMap_standardSection (-a) hφ (p z)] at H
    rw [characterList_eq_blockList, hes] at H
    exact H
  have hz := realPairStripReflection (r + 1) es.length sh sh' p (fun _ => q) eb c hc sign hsign
    hp (differentiable_const q) Z Zd σ hZ hZd hBound ⟨δ, hδ, hInit'⟩
  show HasRealPairNormalizedGrowth (characterList pr (p 1)) es
    ((characterList pr (p 1)).map RealLocalJacquet.dualBlock)
    (es.map RealLocalJacquet.dualBlock) eb c hc sign
    (realUnequalIntegral h D (F (p 1)) V) (realUnequalDualIntegral h b D (F (p 1)) V)
  rw [characterList_eq_blockList, hes]
  exact hz

end Langlands.Global.RankinSelbergGlobal.RealUnequalFamily
