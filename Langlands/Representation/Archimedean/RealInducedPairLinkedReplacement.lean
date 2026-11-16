import Langlands.Representation.Archimedean.RealStandardFiltration
import Langlands.Representation.Archimedean.ComplexJacquetBorel

/-!
# The heavier replacement pair for two linked real induction blocks

The outer and inner endpoint pairings preserve exponent support and strictly increase
squared weights at a positive linked gap. These are arithmetic facts only; no map between
standard modules, occurrence of a subquotient, or filtration is asserted.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.RealInducedPairLinkedReplacement

open Langlands.LocalFactor.Archimedean

/-- Weight of the outer endpoint pair. -/
def outerWeight (d e : ComplexCharacterData) (k : ℕ) : ℕ :=
  max d.weight.natAbs e.weight.natAbs + k + 1

/-- Signed weight of the inner endpoint pair. -/
def innerWeight (d e : ComplexCharacterData) (k : ℕ) : ℤ :=
  (k : ℤ) + 1 - (min d.weight.natAbs e.weight.natAbs : ℕ)

/-- Center of the outer endpoint pair. -/
def outerExponent (d e : ComplexCharacterData) : ℂ :=
  (d.exponent + e.exponent + ((e.weight.natAbs : ℂ) - d.weight.natAbs) / 2) / 2

/-- Center of the inner endpoint pair. -/
def innerExponent (d e : ComplexCharacterData) : ℂ :=
  (d.exponent + e.exponent + ((d.weight.natAbs : ℂ) - e.weight.natAbs) / 2) / 2

/-- The actual complex character with the outer weight and exponent. -/
def outerData (d e : ComplexCharacterData) (k : ℕ) : ComplexCharacterData :=
  characterOfParams (outerWeight d e k : ℤ) (outerExponent d e)

/-- The actual complex character with the signed inner weight and exponent. -/
def innerData (d e : ComplexCharacterData) (k : ℕ) : ComplexCharacterData :=
  characterOfParams (innerWeight d e k) (innerExponent d e)

/-- The ordered outer/inner pair of real induction blocks. -/
def replacementPair (d e : ComplexCharacterData) (k : ℕ) : List RealBlock :=
  [.induced (outerData d e k), .induced (innerData d e k)]

/-- The positive linked-gap equality, with integer subtraction before absolute value. -/
def IsLinkedAt (d e : ComplexCharacterData) (k : ℕ) : Prop :=
  e.exponent - d.exponent =
    (((d.weight.natAbs : ℤ) - (e.weight.natAbs : ℤ)).natAbs : ℂ) / 2 + (k : ℂ) + 1

private theorem cast_abs_sub (L M : ℕ) :
    (((L : ℤ) - (M : ℤ)).natAbs : ℂ) = ((max L M : ℕ) : ℂ) - ((min L M : ℕ) : ℂ) := by
  have h : (((L : ℤ) - (M : ℤ)).natAbs : ℤ) =
      ((max L M : ℕ) : ℤ) - ((min L M : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]
    rcases le_total L M with h | h
    · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (by omega)]
      omega
    · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (by omega)]
  simpa only [Int.cast_natCast, Int.cast_sub] using
    congrArg (fun z : ℤ => (z : ℂ)) h

/-- A linked gap written using maximum and minimum absolute weights. -/
theorem linkedAt_iff (d e : ComplexCharacterData) (k : ℕ) :
    IsLinkedAt d e k ↔ e.exponent - d.exponent =
      (((max d.weight.natAbs e.weight.natAbs : ℕ) : ℂ) -
        ((min d.weight.natAbs e.weight.natAbs : ℕ) : ℂ)) / 2 + (k : ℂ) + 1 := by
  unfold IsLinkedAt
  rw [cast_abs_sub]

/-- Allowing a signed weight changes the two support endpoints only by permutation. -/
theorem signed_support (q : ℤ) (t : ℂ) :
    (realBlockSupport (.induced (characterOfParams q t))).Perm
      [t + (q : ℂ) / 2, t - (q : ℂ) / 2] := by
  have hc : (q.natAbs : ℂ) = (|q| : ℤ) := by
    simpa only [Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : ℂ)) (Int.natCast_natAbs q)
  simp only [realBlockSupport, characterOfParams_weight, characterOfParams_exponent, hc]
  rcases le_total 0 q with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h]
    have h1 : t + ((-q : ℤ) : ℂ) / 2 = t - (q : ℂ) / 2 := by push_cast; ring
    have h2 : t - ((-q : ℤ) : ℂ) / 2 = t + (q : ℂ) / 2 := by push_cast; ring
    rw [h1, h2]
    exact List.Perm.swap _ _ _

/-- The four signed endpoints of the replacement pair are the original outer and inner
endpoints. The inner endpoints may be in either numerical order. -/
theorem endpoint_equalities {d e : ComplexCharacterData} {k : ℕ} (h : IsLinkedAt d e k) :
    outerExponent d e + (outerWeight d e k : ℂ) / 2 =
        e.exponent + (e.weight.natAbs : ℂ) / 2 ∧
    outerExponent d e - (outerWeight d e k : ℂ) / 2 =
        d.exponent - (d.weight.natAbs : ℂ) / 2 ∧
    innerExponent d e + (innerWeight d e k : ℂ) / 2 =
        e.exponent - (e.weight.natAbs : ℂ) / 2 ∧
    innerExponent d e - (innerWeight d e k : ℂ) / 2 =
        d.exponent + (d.weight.natAbs : ℂ) / 2 := by
  have hg := (linkedAt_iff d e k).mp h
  have hm : ((max d.weight.natAbs e.weight.natAbs : ℕ) : ℂ) +
      ((min d.weight.natAbs e.weight.natAbs : ℕ) : ℂ) =
      (d.weight.natAbs : ℂ) + (e.weight.natAbs : ℂ) := by
    exact_mod_cast max_add_min d.weight.natAbs e.weight.natAbs
  dsimp [outerExponent, innerExponent, outerWeight, innerWeight]
  simp only [Nat.cast_add, Nat.cast_one, Int.cast_sub, Int.cast_add, Int.cast_natCast,
    Int.cast_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination -hg / 2 + hm / 4
  · linear_combination hg / 2 - hm / 4
  · linear_combination -hg / 2 - hm / 4
  · linear_combination hg / 2 + hm / 4

/-- The replacement pair has the same complex exponent support as the original pair,
including when the signed inner weight is zero or negative. -/
theorem support_perm {d e : ComplexCharacterData} {k : ℕ} (h : IsLinkedAt d e k) :
    (realExponentSupport (replacementPair d e k)).Perm
      (realExponentSupport [.induced d, .induced e]) := by
  obtain ⟨h1, h2, h3, h4⟩ := endpoint_equalities h
  have hp := (signed_support (outerWeight d e k : ℤ) (outerExponent d e)).append
    (signed_support (innerWeight d e k) (innerExponent d e))
  change ((realBlockSupport (.induced (outerData d e k))) ++
    realBlockSupport (.induced (innerData d e k))).Perm _
  refine hp.trans ?_
  simp only [Int.cast_natCast, h1, h2, h3, h4, List.cons_append, List.nil_append]
  simp only [realExponentSupport, realBlockSupport, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.cons_append, List.nil_append]
  exact ((((List.Perm.swap _ _ []).cons _).cons _).trans
    ((List.Perm.swap _ _ [_]).cons _)).trans
      ((List.Perm.swap _ _ [_, _]).trans ((List.Perm.swap _ _ [_]).cons _))

/-- The exact increase of squared weights, expressed in the integers. -/
theorem weightSquareSum_gap (d e : ComplexCharacterData) (k : ℕ) :
    (realWeightSquareSum (replacementPair d e k) : ℤ) -
      (realWeightSquareSum [.induced d, .induced e] : ℤ) =
    2 * ((k : ℤ) + 1) * (((max d.weight.natAbs e.weight.natAbs : ℕ) : ℤ) -
      ((min d.weight.natAbs e.weight.natAbs : ℕ) : ℤ) + (k : ℤ) + 1) := by
  simp only [replacementPair, realWeightSquareSum, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, realBlockWeightSquare, outerData, innerData,
    characterOfParams_weight, Int.natAbs_natCast, add_zero, Nat.cast_add, Nat.cast_pow]
  dsimp [outerWeight, innerWeight]
  rcases le_total d.weight.natAbs e.weight.natAbs with h | h
  · rw [max_eq_right h, min_eq_left h]
    simp only [Int.natCast_natAbs, sq_abs]
    nlinarith only [sq_abs d.weight, sq_abs e.weight]
  · rw [max_eq_left h, min_eq_right h]
    simp only [Int.natCast_natAbs, sq_abs]
    nlinarith only [sq_abs d.weight, sq_abs e.weight]

/-- Squared weights strictly increase for every natural linked-gap index. This inequality
needs no condition on the original exponents. -/
theorem weightSquareSum_lt (d e : ComplexCharacterData) (k : ℕ) :
    realWeightSquareSum [.induced d, .induced e] <
      realWeightSquareSum (replacementPair d e k) := by
  have hmm : ((min d.weight.natAbs e.weight.natAbs : ℕ) : ℤ) ≤
      ((max d.weight.natAbs e.weight.natAbs : ℕ) : ℤ) := by
    exact_mod_cast min_le_max
  have hp : 0 < 2 * ((k : ℤ) + 1) *
      (((max d.weight.natAbs e.weight.natAbs : ℕ) : ℤ) -
        ((min d.weight.natAbs e.weight.natAbs : ℕ) : ℤ) + (k : ℤ) + 1) := by
    apply mul_pos
    · positivity
    · omega
  have hg := weightSquareSum_gap d e k
  have hi : (realWeightSquareSum [.induced d, .induced e] : ℤ) <
      (realWeightSquareSum (replacementPair d e k) : ℤ) := by omega
  exact_mod_cast hi

/-- Both clauses of the heavier-piece alternative in `RealAdjacentFiltration`. -/
theorem allowed_piece {d e : ComplexCharacterData} {k : ℕ} (h : IsLinkedAt d e k) :
    replacementPair d e k = [.induced e, .induced d] ∨
      ((realExponentSupport (replacementPair d e k)).Perm
        (realExponentSupport [.induced d, .induced e]) ∧
        realWeightSquareSum [.induced d, .induced e] <
          realWeightSquareSum (replacementPair d e k)) :=
  Or.inr ⟨support_perm h, weightSquareSum_lt d e k⟩

/-- The replacement pair is an allowed adjacent piece in arbitrary surrounding lists. -/
theorem isAdjacentPiece (pre post : List RealBlock) {d e : ComplexCharacterData} {k : ℕ}
    (h : IsLinkedAt d e k) :
    RealStandardFiltration.IsAdjacentPiece pre post (.induced d) (.induced e)
      (pre ++ replacementPair d e k ++ post) :=
  ⟨replacementPair d e k, rfl, allowed_piece h⟩

end Langlands.Archimedean.RealInducedPairLinkedReplacement
