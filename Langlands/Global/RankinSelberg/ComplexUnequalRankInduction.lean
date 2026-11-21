import Langlands.Global.RankinSelberg.ComplexAdjacentFromEqual
import Langlands.Global.RankinSelberg.ComplexEqualNormalizedFromCanonical
import Langlands.Global.RankinSelberg.ComplexLocalUnequalFromNormalized

/-! # Induction on the ranks in the complex local functional equation -/

noncomputable section

open scoped SchwartzMap

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal (ComplexQuotientMeasureData complexSelfDualMeasure)
open ComplexJacquetContinuation (HasCanonicalEqualNormalization)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

/-- The equal-rank successor calculation on canonical values with the standard trace character,
given the normalized equation at the adjacent pair of ranks. -/
def ComplexEqualCanonicalSuccessorStatement : Prop :=
  ∀ r : ℕ, ComplexLocalUnequalNormalizedAtRanksStatement (r + 1) r (Nat.lt_succ_self r) →
    ∀ (D : ComplexQuotientMeasureData (r + 1)) (l k : Fin (r + 1 + 1) → ℤ)
      (p q : Fin (r + 1 + 1) → ℂ) (Φ : 𝓢(Fin (r + 1 + 1) → ℂ, ℂ)),
      HasCanonicalEqualNormalization (complexSelfDualMeasure 1) 1 D l k p q Φ

/-- Increase the larger rank by one while holding the smaller rank fixed. -/
def ComplexUnequalNormalizedRankGapStepStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r), ComplexLocalUnequalNormalizedAtRanksStatement r t h →
    ComplexLocalUnequalNormalizedAtRanksStatement (r + 1) t (h.trans (Nat.lt_succ_self r))

/-- The canonical equal-rank successor and the normalized rank-gap step imply
the exact unequal-rank local functional equation. -/
def ComplexUnequalRankInductionStatement : Prop :=
  ComplexEqualCanonicalSuccessorStatement → ComplexUnequalNormalizedRankGapStepStatement →
    ComplexLocalUnequalFunctionalEquationStatement

theorem complexEqualNormalizedInduction (h : ComplexEqualCanonicalSuccessorStatement) :
    ∀ r : ℕ, ComplexLocalEqualNormalizedAtRankStatement r := by
  intro r
  induction r with
  | zero => exact complexEqualNormalizedRankZero
  | succ r ih =>
    exact complexEqualNormalizedFromCanonical (r + 1) (h r (complexAdjacentFromEqual r ih))

theorem complexUnequalRankInduction : ComplexUnequalRankInductionStatement := by
  intro hEqual hGap
  have hAll (r t : ℕ) (h : t < r) : ComplexLocalUnequalNormalizedAtRanksStatement r t h := by
    induction r generalizing t with
    | zero => exact (Nat.not_lt_zero _ h).elim
    | succ r ih =>
      rcases (Nat.lt_succ_iff.mp h).eq_or_lt with h' | h'
      · subst t
        exact complexAdjacentFromEqual r (complexEqualNormalizedInduction hEqual r)
      · exact hGap r t h' (ih t h')
  apply complexLocalUnequalFromNormalized
  intro r t h ds es hd he a D B B' hB hB' f f'
  have hW : B f ∈ complexWhittakerModel r ds a :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)
  have hV : B' f' ∈ complexWhittakerModel t es (-a) :=
    Submodule.mem_iSup_of_mem B' (Submodule.mem_iSup_of_mem hB' ⟨f', rfl⟩)
  obtain ⟨N, Nd, hN, hNd, ⟨σ, hσ⟩, hReflect⟩ :=
    hAll r t h ds es hd he a D (B f) (B' f') hW hV
  exact ⟨σ, N, Nd, hN, hNd, hσ, hReflect⟩

end Langlands.Global.RankinSelbergGlobal
