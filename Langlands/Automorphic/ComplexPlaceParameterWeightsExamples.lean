import Langlands.Automorphic.ComplexPlaceParameterWeights
import Langlands.Representation.Archimedean.ComplexJacquetBorel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Worked complex-place normalization examples

All blocks use the published actual continuous character `characterOfParams`.
The calculations concern exponent coordinates, not embeddings of standard modules.
-/

noncomputable section

universe uF

set_option autoImplicit false

namespace Langlands.Automorphic.ComplexPlaceParameter.Examples

open Langlands.LocalFactor.Archimedean
open Langlands.Archimedean
open Langlands.Global
open NumberField NumberField.InfinitePlace

/-- The actual rank-one character of weight `3` and polar exponent `1/2`. -/
def rankOneData : List ComplexCharacterData :=
  [characterOfParams 3 (1 / 2)]

/-- In rank one the half-sum is zero. -/
theorem rho_one (i : Fin 1) : rho 1 i = 0 := by
  fin_cases i
  norm_num [rho]

/-- The rank-one polar coordinates are `p = 2` and `q = -1`. -/
theorem rankOne_exponents :
    (characterOfParams 3 (1 / 2)).zExponent = 2 ∧
      (characterOfParams 3 (1 / 2)).zBarExponent = -1 := by
  norm_num [ComplexCharacterData.zExponent, ComplexCharacterData.zBarExponent]

/-- The scalar highest weights agree with the rank-one exponent coordinates. -/
theorem rankOne_matches :
    MatchesHighestWeight 1 rankOneData (fun _ => 2) (fun _ => -1) := by
  norm_num [MatchesHighestWeight, rankOneData, List.ofFn_succ, rho,
    ComplexCharacterData.zExponent, ComplexCharacterData.zBarExponent]

/-- The actual rank-one list is regular algebraic in Clozel's coordinate convention. -/
theorem rankOne_regular : IsClozelRegularAlgebraic 1 rankOneData := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro d hd
    have hd' : d = characterOfParams 3 (1 / 2) := List.mem_singleton.mp hd
    subst d
    refine ⟨2, -1, ?_, ?_⟩ <;>
      norm_num [ComplexCharacterData.zExponent, ComplexCharacterData.zBarExponent]
  · simp [rankOneData]
  · simp [rankOneData]

/-- Two actual weight-zero blocks with polar exponents `1/2` and `-1/2`. -/
def rankTwoData : List ComplexCharacterData :=
  [characterOfParams 0 (1 / 2), characterOfParams 0 (-1 / 2)]

/-- The half-sum in rank two is `(1/2, -1/2)`. -/
theorem rho_two : rho 2 0 = 1 / 2 ∧ rho 2 1 = -1 / 2 := by
  norm_num [rho]

/-- Each exponent list of the weight-zero example is `(1/2, -1/2)`. -/
theorem rankTwo_exponents :
    rankTwoData.map ComplexCharacterData.zExponent = [1 / 2, -1 / 2] ∧
      rankTwoData.map ComplexCharacterData.zBarExponent = [1 / 2, -1 / 2] := by
  norm_num [rankTwoData, ComplexCharacterData.zExponent, ComplexCharacterData.zBarExponent]

/-- The two weight-zero blocks match highest weight zero at each embedding. -/
theorem rankTwo_matches :
    MatchesHighestWeight 2 rankTwoData (fun _ => 0) (fun _ => 0) := by
  norm_num [MatchesHighestWeight, rankTwoData, List.ofFn_succ, rho,
    ComplexCharacterData.zExponent, ComplexCharacterData.zBarExponent]

/-- Both rank-two exponent lists lie in `1/2 + ℤ` and have distinct entries. -/
theorem rankTwo_regular : IsClozelRegularAlgebraic 2 rankTwoData := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro d hd
    simp [rankTwoData] at hd
    rcases hd with rfl | rfl
    · refine ⟨0, 0, ?_, ?_⟩ <;>
        norm_num [ComplexCharacterData.zExponent, ComplexCharacterData.zBarExponent]
    · refine ⟨-1, -1, ?_, ?_⟩ <;>
        norm_num [ComplexCharacterData.zExponent, ComplexCharacterData.zBarExponent]
  · norm_num [rankTwoData, ComplexCharacterData.zExponent]
  · norm_num [rankTwoData, ComplexCharacterData.zBarExponent]

/-- Two actual trivial characters, for comparison with the shifted weight-zero list. -/
def twoTrivialData : List ComplexCharacterData :=
  [characterOfParams 0 0, characterOfParams 0 0]

/-- Repeated exponent coordinates obstruct Clozel regularity. -/
theorem twoTrivial_not_regular : ¬ IsClozelRegularAlgebraic 2 twoTrivialData := by
  simp [IsClozelRegularAlgebraic, twoTrivialData]

/-- The two rank-two blocks for the embedding-orientation calculation. -/
def orientationData : List ComplexCharacterData :=
  [characterOfParams 1 2, characterOfParams 1 (-1)]

/-- The z coordinates are `(5/2,-1/2)` and conjugate-z coordinates `(3/2,-3/2)`. -/
theorem orientation_exponents :
    orientationData.map ComplexCharacterData.zExponent = [5 / 2, -1 / 2] ∧
      orientationData.map ComplexCharacterData.zBarExponent = [3 / 2, -3 / 2] := by
  norm_num [orientationData, ComplexCharacterData.zExponent, ComplexCharacterData.zBarExponent]

/-- The two highest weights are `(2,0)` at z and `(1,-1)` at conjugate z. -/
theorem orientation_matches :
    MatchesHighestWeight 2 orientationData ![2, 0] ![1, -1] := by
  norm_num [MatchesHighestWeight, orientationData, List.ofFn_succ, rho,
    ComplexCharacterData.zExponent, ComplexCharacterData.zBarExponent]

/-- The orientation example also has separate regularity and both integrality cosets. -/
theorem orientation_regular : IsClozelRegularAlgebraic 2 orientationData := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro d hd
    simp [orientationData] at hd
    rcases hd with rfl | rfl
    · refine ⟨2, 1, ?_, ?_⟩ <;>
        norm_num [ComplexCharacterData.zExponent, ComplexCharacterData.zBarExponent]
    · refine ⟨-1, -2, ?_, ?_⟩ <;>
        norm_num [ComplexCharacterData.zExponent, ComplexCharacterData.zBarExponent]
  · norm_num [orientationData, ComplexCharacterData.zExponent]
  · norm_num [orientationData, ComplexCharacterData.zBarExponent]

variable (F : Type uF) [Field F]

/-- Direct reuse of the published theorem: `false` reads the z component. -/
theorem embedding_false_reads_z
    (v : {v : NumberField.InfinitePlace F // IsComplex v})
    (x : mixedEmbedding.mixedSpace F) :
    ArchimedeanGL.embeddingComponent F (.inr (v, false)) x = x.2 v :=
  ArchimedeanGL.embeddingComponent_inr_false F v x

/-- Direct reuse of the published theorem: `true` reads the conjugate-z component. -/
theorem embedding_true_reads_zBar
    (v : {v : NumberField.InfinitePlace F // IsComplex v})
    (x : mixedEmbedding.mixedSpace F) :
    ArchimedeanGL.embeddingComponent F (.inr (v, true)) x =
      (starRingEnd ℂ) (x.2 v) :=
  ArchimedeanGL.embeddingComponent_inr_true F v x

variable [NumberField F]

/-- Global weights for the orientation example; real indices are chosen as zero. -/
def orientationHighestWeight : ArchimedeanGL.EmbeddingIndex F → Fin 2 → ℂ
  | .inl _ => fun _ => 0
  | .inr (_, false) => ![2, 0]
  | .inr (_, true) => ![1, -1]

/-- The global relation uses `(2,0)` at false and `(1,-1)` at true, as above. -/
theorem orientation_matchesGlobal :
    MatchesGlobalHighestWeight F 2 (fun _ => orientationData) (orientationHighestWeight F) := by
  intro v
  exact orientation_matches

end Langlands.Automorphic.ComplexPlaceParameter.Examples
