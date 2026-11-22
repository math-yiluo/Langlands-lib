import Langlands.Global.RankinSelberg.RealLocalEqualGeneratorTrace
import Langlands.Global.RankinSelberg.RealGodementCanonicalModel

/-! # The real equal-rank normalized equation on the canonical range -/

noncomputable section

open MeasureTheory Set
open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open scoped NNReal SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open ArchimedeanLocal
open Langlands.Archimedean.RealJacquetFrobenius (charData)

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
private local instance (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) :=
  ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

attribute [local instance 100] LieRing.ofAssociativeRing

private local instance (n : ℕ) (ds : List RealBlock) :
    NormedAddCommGroup (RealStandardCompactBanach.Carrier n ds) :=
  (RealStandardCompactBanach.closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) :
    NormedSpace ℂ (RealStandardCompactBanach.Carrier n ds) :=
  (RealStandardCompactBanach.closureSubmodule (n := n) ds).normedSpace

variable {t : ℕ}

local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "Row" => (Fin (t + 2) → ℝ)

/-! ### Coefficients with the normalized equal-rank equation -/

private theorem realEqualIntegrand_add (W₁ W₂ V : H → ℂ) (φ : Row → ℂ) (s : ℂ) :
    realEqualIntegrand (W₁ + W₂) V φ s = realEqualIntegrand W₁ V φ s + realEqualIntegrand W₂ V φ s := by
  funext q
  simp only [realEqualIntegrand, ArchimedeanLocal.equalIntegrand, Pi.add_apply]
  ring

private theorem realEqualIntegrand_smul (c : ℂ) (W V : H → ℂ) (φ : Row → ℂ) (s : ℂ) :
    realEqualIntegrand (c • W) V φ s = c • realEqualIntegrand W V φ s := by
  funext q
  simp only [realEqualIntegrand, ArchimedeanLocal.equalIntegrand, Pi.smul_apply, smul_eq_mul]
  ring

private theorem dualFunction_add (W₁ W₂ : H → ℂ) :
    ArchimedeanLocal.dualFunction (t + 2) (W₁ + W₂) =
      ArchimedeanLocal.dualFunction (t + 2) W₁ + ArchimedeanLocal.dualFunction (t + 2) W₂ := rfl

private theorem dualFunction_smul (c : ℂ) (W : H → ℂ) :
    ArchimedeanLocal.dualFunction (t + 2) (c • W) = c • ArchimedeanLocal.dualFunction (t + 2) W := rfl

variable (t) in
/-- The coefficients `W` of `GL_{t+2}(ℝ)` whose real equal-rank integral against `(V, φ)` and
whose dual integral (parameter `b`) converge absolutely on a right half-plane and satisfy the
normalized equation `HasRealPairNormalizedGrowth` with the given data. They form a complex
subspace. -/
def equalGrowthSubmodule (D' : RealQuotientMeasureData (t + 1)) (b : ℝˣ) (V : H → ℂ)
    (φ : Row → ℂ) (xs ys xsd ysd : List RealBlock) (bb : ℝˣ) (c : ℝ≥0) (hc : 0 < c)
    (sign : ℂ) : Submodule ℂ (H → ℂ) where
  carrier := {W | ∃ σ : ℝ, (∀ s : ℂ, σ < s.re →
      Integrable (realEqualIntegrand W V φ s) D'.measure ∧
      Integrable (realEqualIntegrand (ArchimedeanLocal.dualFunction (t + 2) W)
        (ArchimedeanLocal.dualFunction (t + 2) V) (realFourierTransform b φ) s) D'.measure) ∧
    RealJacquet.HasRealPairNormalizedGrowth xs ys xsd ysd bb c hc sign
      (realEqualIntegral D' W V φ) (realEqualDualIntegral b D' W V φ)}
  zero_mem' := by
    refine ⟨0, fun s _ => ⟨?_, ?_⟩, ?_⟩
    · have h : realEqualIntegrand (0 : H → ℂ) V φ s = 0 := by
        funext q
        simp [realEqualIntegrand, ArchimedeanLocal.equalIntegrand]
      rw [h]
      exact integrable_zero _ _ _
    · have h : realEqualIntegrand (ArchimedeanLocal.dualFunction (t + 2) (0 : H → ℂ))
          (ArchimedeanLocal.dualFunction (t + 2) V) (realFourierTransform b φ) s = 0 := by
        funext q
        simp [realEqualIntegrand, ArchimedeanLocal.equalIntegrand, ArchimedeanLocal.dualFunction]
      rw [h]
      exact integrable_zero _ _ _
    · refine RealJacquet.HasRealPairNormalizedGrowth.zero.congr (τ := 0) (fun s _ => ?_) (fun s _ => ?_)
      · simp [realEqualIntegral, ArchimedeanLocal.equalIntegral, ArchimedeanLocal.equalIntegrand]
      · simp [realEqualDualIntegral, ArchimedeanLocal.equalIntegral, ArchimedeanLocal.equalIntegrand,
          ArchimedeanLocal.dualFunction]
  add_mem' := by
    rintro W₁ W₂ ⟨σ₁, hI₁, hG₁⟩ ⟨σ₂, hI₂, hG₂⟩
    refine ⟨max σ₁ σ₂, fun s hs => ?_, ?_⟩
    · obtain ⟨a₁, b₁⟩ := hI₁ s ((le_max_left _ _).trans_lt hs)
      obtain ⟨a₂, b₂⟩ := hI₂ s ((le_max_right _ _).trans_lt hs)
      rw [realEqualIntegrand_add, dualFunction_add, realEqualIntegrand_add]
      exact ⟨a₁.add a₂, b₁.add b₂⟩
    · refine (hG₁.add hG₂).congr (τ := max σ₁ σ₂) (fun s hs => ?_) (fun s hs => ?_)
      · obtain ⟨a₁, -⟩ := hI₁ s ((le_max_left _ _).trans_lt hs)
        obtain ⟨a₂, -⟩ := hI₂ s ((le_max_right _ _).trans_lt hs)
        change realEqualIntegral D' W₁ V φ s + realEqualIntegral D' W₂ V φ s =
          realEqualIntegral D' (W₁ + W₂) V φ s
        unfold realEqualIntegral ArchimedeanLocal.equalIntegral
        change (∫ q, realEqualIntegrand W₁ V φ s q ∂D'.measure) +
            (∫ q, realEqualIntegrand W₂ V φ s q ∂D'.measure) =
          ∫ q, realEqualIntegrand (W₁ + W₂) V φ s q ∂D'.measure
        rw [realEqualIntegrand_add]
        exact (integral_add a₁ a₂).symm
      · obtain ⟨-, b₁⟩ := hI₁ s ((le_max_left _ _).trans_lt hs)
        obtain ⟨-, b₂⟩ := hI₂ s ((le_max_right _ _).trans_lt hs)
        change realEqualDualIntegral b D' W₁ V φ s + realEqualDualIntegral b D' W₂ V φ s =
          realEqualDualIntegral b D' (W₁ + W₂) V φ s
        unfold realEqualDualIntegral ArchimedeanLocal.equalIntegral
        change (∫ q, realEqualIntegrand (ArchimedeanLocal.dualFunction (t + 2) W₁)
              (ArchimedeanLocal.dualFunction (t + 2) V) (realFourierTransform b φ) s q ∂D'.measure) +
            (∫ q, realEqualIntegrand (ArchimedeanLocal.dualFunction (t + 2) W₂)
              (ArchimedeanLocal.dualFunction (t + 2) V) (realFourierTransform b φ) s q ∂D'.measure) =
          ∫ q, realEqualIntegrand (ArchimedeanLocal.dualFunction (t + 2) (W₁ + W₂))
            (ArchimedeanLocal.dualFunction (t + 2) V) (realFourierTransform b φ) s q ∂D'.measure
        rw [dualFunction_add, realEqualIntegrand_add]
        exact (integral_add b₁ b₂).symm
  smul_mem' := by
    rintro c₀ W ⟨σ, hI, hG⟩
    refine ⟨σ, fun s hs => ?_, ?_⟩
    · obtain ⟨a₁, b₁⟩ := hI s hs
      rw [realEqualIntegrand_smul, dualFunction_smul, realEqualIntegrand_smul]
      exact ⟨a₁.smul c₀, b₁.smul c₀⟩
    · refine (hG.const_mul c₀).congr (τ := σ) (fun s _ => ?_) (fun s _ => ?_)
      · change c₀ * realEqualIntegral D' W V φ s = realEqualIntegral D' (c₀ • W) V φ s
        unfold realEqualIntegral ArchimedeanLocal.equalIntegral
        change c₀ * (∫ q, realEqualIntegrand W V φ s q ∂D'.measure) =
          ∫ q, realEqualIntegrand (c₀ • W) V φ s q ∂D'.measure
        rw [realEqualIntegrand_smul]
        simp only [Pi.smul_apply, smul_eq_mul]
        exact (integral_const_mul c₀ _).symm
      · change c₀ * realEqualDualIntegral b D' W V φ s = realEqualDualIntegral b D' (c₀ • W) V φ s
        unfold realEqualDualIntegral ArchimedeanLocal.equalIntegral
        change c₀ * (∫ q, realEqualIntegrand (ArchimedeanLocal.dualFunction (t + 2) W)
              (ArchimedeanLocal.dualFunction (t + 2) V) (realFourierTransform b φ) s q ∂D'.measure) =
          ∫ q, realEqualIntegrand (ArchimedeanLocal.dualFunction (t + 2) (c₀ • W))
            (ArchimedeanLocal.dualFunction (t + 2) V) (realFourierTransform b φ) s q ∂D'.measure
        rw [dualFunction_smul, realEqualIntegrand_smul]
        simp only [Pi.smul_apply, smul_eq_mul]
        exact (integral_const_mul c₀ _).symm


/-! ### The canonical range -/

variable (t) in
/-- Let `W` be a canonical real Whittaker coefficient of rank `t + 2` for the character
list `characterList P Zs` with character `a` (the canonical map for `-a`), and let `B f` be a
coefficient of a uniform Whittaker map for a character list `fs` with character `-a` admitting a
continuous Whittaker evaluation. Assume the corank-one normalized equation at rank `t` for the
tail list against `fs`, and the matrix normalized equation for orthogonal-finite tests. Then the
real equal-rank integral of `(W, B f, φ)` and its dual satisfy the normalized equal-rank equation
with strip growth. -/
def RealLocalEqualCanonicalGrowthStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (D' : RealQuotientMeasureData (t + 1)) (a : ℝˣ)
    (P : Fin (t + 2) → Fin 2) (Zs : Fin (t + 2) → ℂ) (fs : List RealCharacterData),
    fs.length = t + 2 →
  ∀ (F : Automorphic.realStandardKFinite (t + 2) (RealGodementProfiles.characterList P Zs))
    (B : Automorphic.realStandardKFinite (t + 2) (fs.map RealBlock.character) →ₗ[ℂ] (H → ℂ)),
    IsRealUniformWhittakerIntertwiner (t + 1) (fs.map RealBlock.character) (-a) B →
    (∃ L : DerivativeSmoothVectors (matrixModel ℝ (t + 2))
        (RealStandardCompactBanach.representation (n := t + 2) (fs.map RealBlock.character)) →L[ℂ] ℂ,
      RealStandardCompactBanach.IsWhittakerStandardEvaluation (fs.map RealBlock.character) (-a) B L) →
  ∀ (f : Automorphic.realStandardKFinite (t + 2) (fs.map RealBlock.character))
    (φ : 𝓢(Row, ℂ)),
    (∀ U ∈ realUniformWhittakerModel t
        ((List.ofFn fun i : Fin (t + 1) => charData (P i.succ) (Zs i.succ)).map RealBlock.character) a,
      ∀ V ∈ realUniformWhittakerModel (t + 1) (fs.map RealBlock.character) (-a),
      RealJacquet.HasRealPairNormalizedGrowth (fs.map RealBlock.character)
        ((List.ofFn fun i : Fin (t + 1) => charData (P i.succ) (Zs i.succ)).map RealBlock.character)
        ((fs.map RealBlock.character).map RealLocalJacquet.dualBlock)
        (((List.ofFn fun i : Fin (t + 1) => charData (P i.succ) (Zs i.succ)).map
          RealBlock.character).map RealLocalJacquet.dualBlock) a
        (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
        ((RealJacquet.determinant (fs.map RealBlock.character) (-1) : ℂ) ^ (t + 1) *
          (RealJacquet.determinant ((List.ofFn fun i : Fin (t + 1) =>
            charData (P i.succ) (Zs i.succ)).map RealBlock.character) (-1) : ℂ))
        (realUnequalIntegral (Nat.lt_succ_self t) D V U)
        (realUnequalDualIntegral (Nat.lt_succ_self t) (-a) D V U)) →
    (∀ Ψ : 𝓢(Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ, ℂ),
      FiniteDimensional ℂ (Submodule.span ℂ (range fun k : unitaryCompact ℝ (t + 2) =>
        fun X' : Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ => Ψ (k.val⁻¹.val * X'))) →
      RealMatrixCoefficientNormalizedGrowth t D' a (P 0) (fs.map RealBlock.character) f Ψ
        [RealBlock.character (charData (P 0) 0)] (fs.map RealBlock.character)
        ([RealBlock.character (charData (P 0) 0)].map RealLocalJacquet.dualBlock)
        ((fs.map RealBlock.character).map RealLocalJacquet.dualBlock) (-a)
        (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) 1) →
    RealJacquet.HasRealPairNormalizedGrowth (RealGodementProfiles.characterList P Zs)
      (fs.map RealBlock.character)
      ((RealGodementProfiles.characterList P Zs).map RealLocalJacquet.dualBlock)
      ((fs.map RealBlock.character).map RealLocalJacquet.dualBlock) (-a)
      (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
      ((RealJacquet.determinant (RealGodementProfiles.characterList P Zs) (-1) : ℂ) ^ (t + 1))
      (realEqualIntegral D' (canonicalJacquetMap (-a) P Zs F) (B f) φ)
      (realEqualDualIntegral (-a) D' (canonicalJacquetMap (-a) P Zs F) (B f) φ)

set_option maxHeartbeats 1000000 in
theorem realLocalEqualCanonicalGrowth : RealLocalEqualCanonicalGrowthStatement t := by
  intro D D' a P Zs fs hfs F B hB hL f φ hAdj hMat
  let cs : List RealCharacterData := List.ofFn fun i : Fin (t + 1) => charData (P i.succ) (Zs i.succ)
  have hcs : cs.length = t + 1 := List.length_ofFn
  have hList : RealGodementProfiles.characterList P Zs =
      RealBlock.character (charData (P 0) (Zs 0)) :: cs.map RealBlock.character := by
    simp only [RealGodementProfiles.characterList, List.ofFn_succ, List.map_cons, cs]
  have hV : B f ∈ realUniformWhittakerModel (t + 1) (fs.map RealBlock.character) (-a) :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)
  let M := equalGrowthSubmodule t D' (-a) (B f) φ (RealGodementProfiles.characterList P Zs)
    (fs.map RealBlock.character)
    ((RealGodementProfiles.characterList P Zs).map RealLocalJacquet.dualBlock)
    ((fs.map RealBlock.character).map RealLocalJacquet.dualBlock) (-a)
    (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
    ((RealJacquet.determinant (RealGodementProfiles.characterList P Zs) (-1) : ℂ) ^ (t + 1))
  have hGen : Submodule.span ℂ (compactReflectedColumnGenerators D (-a) cs (P 0) (Zs 0)) ≤
      M.comap (LinearMap.fst ℂ (H → ℂ) (H → ℂ)) := by
    refine Submodule.span_le.mpr ?_
    rintro Q ⟨U, S, Φ, hU, -, hS, hRank, hΦ, rfl⟩
    have hU' : U ∈ realUniformWhittakerModel t (cs.map RealBlock.character) a := by
      simpa only [neg_neg] using hU
    obtain ⟨σ, hI, -, -⟩ := realLocalEqualGeneratorFamily D D' (-a) (-a) (cs.map RealBlock.character)
      (fs.map RealBlock.character) U hU (B f) hV (P 0) S hS hRank Φ hΦ φ (‖Zs 0‖ + 1)
    have hz : Zs 0 ∈ Metric.ball (0 : ℂ) (‖Zs 0‖ + 1) := by
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    have hG := realLocalEqualGeneratorTrace D D' a (P 0) cs fs hcs hfs U hU' B hB hL f S hS hRank
      Φ hΦ φ (hAdj U hU') hMat (Zs 0)
    rw [← hList] at hG
    exact ⟨σ, fun s hs => hI (Zs 0) hz s hs, hG⟩
  have hW := hGen (canonicalJacquetMap_reflectedPair_mem_span D (-a) P Zs F)
  obtain ⟨σ, -, hG⟩ := hW
  exact hG

end Langlands.Global.RankinSelbergGlobal.RealGodement
