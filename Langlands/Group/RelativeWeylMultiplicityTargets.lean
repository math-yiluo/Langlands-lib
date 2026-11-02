import Langlands.Group.RelativeWeylConjugation
import Langlands.Group.RelativeWeylIndexingTargets

/-!
# Actual Levi multiplicities and the Weyl equality-test bridge

The quotient action makes the actual subgroup intersection independent of
normalizer lifts. Comparing its equality test with the intrinsic Weyl test
is a separate proposition, not a consequence of lift independence.
-/

namespace Langlands.Group.RelativeWeylIndexing

universe u v

open scoped BigOperators

noncomputable section

open Classical

variable {B : Type u} {G : Type v} [Group G]
variable {M : CoxeterMatrix B} (T : Subgroup G)
variable (L : Finset B → RelativeWeyl.CentralizerOvergroup T)
variable (actual : ActualCoxeterSystem T M)

/-- The actual source-side intersection `L_J ∩ w⁻¹ L_I w`, using the
lift-independent Weyl action on subgroups containing the centralizer. -/
def actualRightIntersection (I J : Finset B) (w : RelativeWeyl.Weyl T) :
    Subgroup G :=
  (L J).val ⊓ (RelativeWeyl.weylConjugate T w⁻¹ (L I)).val

/-- Every specified lift gives the source's actual subgroup formula. -/
@[simp]
theorem actualRightIntersection_mk (I J : Finset B)
    (n : RelativeWeyl.normalizer T) :
    actualRightIntersection T L I J (QuotientGroup.mk n) =
      (L J).val ⊓ (L I).val.map (MulAut.conj ((n : G)⁻¹) : G →* G) :=
  rfl

/-- Aubert's `a_{J,I,K}` counts actual Levi-intersection equalities. -/
def actualIntersectionMultiplicity [Fintype (RelativeWeyl.Weyl T)]
    (J I K : Finset B) : ℕ :=
  ((minimalReps actual I J).filter (fun w =>
    actualRightIntersection T L I J w = (L K).val)).card

/-- The pointwise realization bridge needed to identify the source's actual
Levi multiplicity with the intrinsic Weyl-subgroup multiplicity. -/
def actualIntersectionEqualityCriterion : Prop :=
  ∀ (I J K : Finset B) (w : RelativeWeyl.Weyl T),
    IsMinimal actual I J w → K ⊆ J →
      (actualRightIntersection T L I J w = (L K).val ↔
        rightIntersection actual I J w = standardSubgroup actual K)

/-- The equality of the two finite counts, with the source's `K ⊆ J`
hypothesis visible. -/
def actualMultiplicityComparison [Fintype (RelativeWeyl.Weyl T)] : Prop :=
  ∀ J I K : Finset B, K ⊆ J →
    actualIntersectionMultiplicity T L actual J I K =
      intersectionMultiplicity actual J I K

/-- Equal pointwise tests give equal finite counts; this does not establish
the realization criterion itself. -/
theorem actualMultiplicityComparison_of_equalityCriterion
    [Fintype (RelativeWeyl.Weyl T)]
    (h : actualIntersectionEqualityCriterion T L actual) :
    actualMultiplicityComparison T L actual := by
  intro J I K hK
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro w hw
  exact h I J K w ((mem_minimalReps actual I J w).mp hw) hK

/-- The signed coefficient identity with the source's actual Levi
multiplicities, separate from the intrinsic finite Weyl target. -/
def actualSolomonCancellation [Fintype B]
    [Fintype (RelativeWeyl.Weyl T)] : Prop :=
  ∀ J K : Finset B, K ⊆ J →
    (∑ I : Finset B, (-1 : ℤ) ^ I.card *
      (actualIntersectionMultiplicity T L actual J I K : ℤ)) =
        (-1 : ℤ) ^ K.card

end

end Langlands.Group.RelativeWeylIndexing
