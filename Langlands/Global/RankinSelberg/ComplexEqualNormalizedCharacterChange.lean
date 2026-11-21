import Langlands.Global.RankinSelberg.ComplexEqualNormalizedRankZero
import Langlands.Global.RankinSelberg.ComplexLocalEqualCharacterReduction

/-! # Change of trace character in the normalized equal-rank equation -/

noncomputable section

open scoped NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal ComplexCharacterChange Langlands.LocalFactor.Archimedean

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

/-- The entire-normalized standard-character statement at one rank yields the
entire-normalized statement for all nonzero trace-character parameters at that rank. -/
def ComplexEqualNormalizedCharacterChangeStatement : Prop :=
  ∀ r : ℕ, ComplexLocalEqualNormalizedAtRankCharacterStatement r 1 →
    ComplexLocalEqualNormalizedAtRankStatement r

theorem complexEqualNormalizedCharacterChange : ComplexEqualNormalizedCharacterChangeStatement := by
  intro r h a ds es hd he D W V Φ hW hV
  let W₁ := normalizeWhittaker a W
  let V₁ := normalizeWhittaker a V
  let D₁ := changeQuotientMeasure a D
  obtain ⟨⟨σ, hI⟩, N, Nd, hN, hNd, ⟨τ, hτ⟩, hE⟩ :=
    h ds es hd he D₁ W₁ V₁ Φ (normalizeWhittaker_mem hW) (normalizeWhittaker_neg_mem hV)
  let c := primalMultiplier r a
  let cd := dualMultiplier r ds es a
  refine ⟨⟨σ, fun s hs => ?_⟩, (fun s => c s * N s), (fun s => cd s * Nd s),
    (differentiable_primalMultiplier r a).mul hN, (differentiable_dualMultiplier r ds es a).mul hNd,
    ⟨τ, fun s hs => ?_⟩, fun s => ?_⟩
  · exact ⟨(primal_comparison hW hV D Φ s).1.mpr (hI s hs).1,
      (dual_comparison hd he hW hV D Φ s).1.mpr (hI s hs).2⟩
  · constructor
    · change c s * N s = _
      rw [(hτ s hs).1, (primal_comparison hW hV D Φ s).2]
      change c s * _ = _ * (c s * _)
      ring
    · change cd s * Nd s = _
      rw [(hτ s hs).2, (dual_comparison hd he hW hV D Φ s).2]
      change cd s * _ = _ * (cd s * _)
      ring
  · let E := (complexPairEpsilon ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ)
    let E₁ := (complexPairEpsilon ds es 1 ‖(↑(1 : ℂˣ) : ℂ)‖₊
      (nnnorm_pos.mpr (1 : ℂˣ).ne_zero) s : ℂ)
    let sign := complexCentralSign es ^ r
    have heps : E * c s = cd (1 - s) * E₁ := epsilon_mul_primal_eq_dual_mul_standard hd he a s
    change cd (1 - s) * Nd (1 - s) = sign * E * (c s * N s)
    calc
      _ = sign * (cd (1 - s) * E₁) * N s := by rw [hE s]; dsimp only [E₁, sign]; ring
      _ = _ := by rw [← heps]; ring

end Langlands.Global.RankinSelbergGlobal
