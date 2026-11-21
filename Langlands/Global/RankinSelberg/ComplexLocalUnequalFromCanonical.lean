import Langlands.Global.RankinSelberg.ComplexJacquetMultiplicityOne
import Langlands.Global.RankinSelberg.ComplexLocalUnequalFromNormalized

/-! # Reduction of the unequal-rank local equation to canonical Jacquet pairs -/

noncomputable section

open scoped Classical Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal
open ArchimedeanLocal

open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexStandardMeasure complexPairLFactor
  complexPairEpsilon)
open ComplexCompactProfileFamily (characterList)
open ComplexJacquetContinuation (continuedJacquet)
open ComplexJacquetMultiplicityOne (complexJacquetMultiplicityOne exists_characterList)

/-- The normalized exact local equation for canonical Jacquet pairs with the fixed
complex additive Haar normalization. -/
def ComplexUnequalCanonicalNormalizedEquationStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (l : Fin (r + 1) → ℤ) (p : Fin (r + 1) → ℂ)
    (l' : Fin (t + 1) → ℤ) (p' : Fin (t + 1) → ℂ) (a : ℂˣ) (D : ComplexQuotientMeasureData t)
    (f : Automorphic.complexStandardKFinite (r + 1) (characterList l p))
    (f' : Automorphic.complexStandardKFinite (t + 1) (characterList l' p')),
    let d := characterList l p
    let d' := characterList l' p'
    let W := continuedJacquet complexStandardMeasure (-a) l p f
    let W' := continuedJacquet complexStandardMeasure a l' p' f'
    ∃ (σ : ℝ) (N Nd : ℂ → ℂ),
      Differentiable ℂ N ∧ Differentiable ℂ Nd ∧
      (∀ s : ℂ, σ < s.re →
        N s = (complexPairLFactor d d').denominator s * complexUnequalIntegral h D W W' s ∧
        Nd s = (complexPairLFactor (d.map ComplexCharacterData.inv)
          (d'.map ComplexCharacterData.inv)).denominator s * complexUnequalDualIntegral h a D W W' s) ∧
      ∀ s : ℂ, Nd (1 - s) = complexCentralSign d' ^ r *
        (complexPairEpsilon d d' a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) * N s

/-- Exact multiplicity one transfers the normalized canonical equation to all exact
intertwiner values. -/
theorem complexUnequalNormalizedFromCanonical :
    ComplexUnequalCanonicalNormalizedEquationStatement → ComplexUnequalNormalizedIntertwinerEquationStatement := by
  intro hCanonical r t h d d' hd hd' a D B B' hB hB' f f'
  obtain ⟨l, p, hl⟩ := exists_characterList d hd
  obtain ⟨l', p', hl'⟩ := exists_characterList d' hd'
  subst d
  subst d'
  obtain ⟨c, hc⟩ := (complexJacquetMultiplicityOne r complexStandardMeasure (-a) l p).1 B
    (by simpa only [neg_neg] using hB)
  obtain ⟨c', hc'⟩ := (complexJacquetMultiplicityOne t complexStandardMeasure a l' p').1 B' hB'
  have hW : continuedJacquet complexStandardMeasure (-a) l p (c • f) = B f := by
    rw [hc, map_smul]
    rfl
  have hW' : continuedJacquet complexStandardMeasure a l' p' (c' • f') = B' f' := by
    rw [hc', map_smul]
    rfl
  have hEq := hCanonical r t h l p l' p' a D (c • f) (c' • f')
  dsimp only at hEq
  rwa [hW, hW'] at hEq

/-- The all-parameter normalized canonical equation implies the exact published local
unequal-rank theorem. -/
def ComplexLocalUnequalFromCanonicalStatement : Prop :=
  ComplexUnequalCanonicalNormalizedEquationStatement → ComplexLocalUnequalFunctionalEquationStatement

theorem complexLocalUnequalFromCanonical : ComplexLocalUnequalFromCanonicalStatement :=
  fun h => complexLocalUnequalFromNormalized (complexUnequalNormalizedFromCanonical h)

end Langlands.Global.RankinSelbergGlobal
