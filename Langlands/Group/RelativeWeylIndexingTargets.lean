import Langlands.Group.RelativeWeylIndexing
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset

/-!
# Finite relative-Weyl cancellation and realization targets

These are propositions, not assumptions bundled into construction data. The
intrinsic targets are distinct from the actual subgroup realization targets.
-/

namespace Langlands.Group.RelativeWeylIndexing

universe u v

open scoped BigOperators

noncomputable section

open Classical

variable {B : Type u} {W : Type v} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- The Coxeter comparison between whole-double-coset minimality and the
simple length inequalities. -/
def minimalityLengthCriterion : Prop :=
  ∀ (I J : Finset B) (w : W), IsMinimal cs I J w ↔
    (∀ i ∈ I, cs.length w < cs.length (cs.simple i * w)) ∧
    (∀ j ∈ J, cs.length w < cs.length (w * cs.simple j))

/-- Uniqueness of the least-length representative in an actual double coset. -/
def minimalRepresentativeUnique : Prop :=
  ∀ (I J : Finset B) (w x y : W),
    x ∈ doubleCoset cs I J w → y ∈ doubleCoset cs I J w →
    IsMinimal cs I J x → IsMinimal cs I J y → x = y

/-- A minimal representative has a standard source-side intersection. -/
def standardIntersection : Prop :=
  ∀ (I J : Finset B) (w : W), IsMinimal cs I J w →
    rightIntersection cs I J w =
      standardSubgroup cs (intersectionSubset cs I J w)

/-- The source's multiplicity `a_{J,I,K}`, expressed intrinsically by equality
of the corresponding standard Weyl subgroups. -/
def intersectionMultiplicity [Fintype W] (J I K : Finset B) : ℕ :=
  ((minimalReps cs I J).filter (fun w =>
    rightIntersection cs I J w = standardSubgroup cs K)).card

/-- Solomon's alternating multiplicity identity used after Aubert (1.8). -/
def solomonCancellation [Fintype B] [Fintype W] : Prop :=
  ∀ (J K : Finset B), K ⊆ J →
    (∑ I : Finset B, (-1 : ℤ) ^ I.card *
      (intersectionMultiplicity cs J I K : ℤ)) = (-1 : ℤ) ^ K.card

/-- The Boolean cancellation within the inner sum of Aubert (1.9). -/
def jacquetCancellation [Fintype B] [Fintype W] : Prop :=
  ∀ (J : Finset B) (w : W), IsMinimal cs J ∅ w →
    ∀ (K : Finset B), K ⊆ J →
      (∑ I ∈ (positiveSimpleSet cs w).powerset,
        if simpleImage cs w I ∩ J = K then (-1 : ℤ) ^ I.card else 0) =
      if MapsIntoSimple cs w (positiveSimpleSet cs w) J
      then (-1 : ℤ) ^ K.card else 0

/-- The maximal-length element of `D(J,∅)` is unique. -/
def longestRepresentativeUnique [Fintype W] : Prop :=
  ∀ (J : Finset B) (w : W),
    w ∈ minimalReps cs J ∅ →
    (∀ x ∈ minimalReps cs J ∅, cs.length x ≤ cs.length w) →
    w = longestRep cs J

/-- Only the source's longest representative survives Jacquet cancellation. -/
def longestSurvivor [Fintype B] [Fintype W] : Prop :=
  ∀ (J : Finset B) (w : W), IsMinimal cs J ∅ w →
    (MapsIntoSimple cs w (positiveSimpleSet cs w) J ↔ w = longestRep cs J)

/-- The inverse longest representative maps `J` to a simple subset of equal
cardinality and conjugates its generated subgroup onto that subset's group. -/
def associatedSubsetLaws [Fintype B] [Fintype W] : Prop :=
  ∀ J : Finset B,
    MapsIntoSimple cs (longestRep cs J)⁻¹ J Finset.univ ∧
    (associatedSubset cs J).card = J.card ∧
    standardSubgroup cs (associatedSubset cs J) =
      conjugateStandardSubgroup cs J (longestRep cs J)⁻¹

section ActualQuotient

variable {G : Type v} [Group G] (T : Subgroup G)
variable (L : Finset B → Subgroup G)
variable (actual : ActualCoxeterSystem T M)

/-- The generated Coxeter subgroup is the image of the actual Levi Weyl
quotient, under the actual injective quotient homomorphism. -/
def actualLeviWeylIdentification : Prop :=
  ∀ I : Finset B,
    (RelativeWeyl.inclusion T (L I)).range = standardSubgroup actual I

/-- The rational-point source intersection agrees with the constructed
standard subset. Every lift is quantified, rather than chosen invisibly. -/
def actualLeviIntersection : Prop :=
  ∀ (I J : Finset B) (w : RelativeWeyl.Weyl T),
    IsMinimal actual I J w →
    ∀ n : RelativeWeyl.normalizer T, QuotientGroup.mk n = w →
      L J ⊓ (L I).map (MulAut.conj ((n : G)⁻¹) : G →* G) =
        L (intersectionSubset actual I J w)

/-- The associated-Levi transport uses conjugation by a lift of `w_J`,
from the Levi of `w_J⁻¹(J)` to the Levi of `J`. -/
def actualAssociatedLeviConjugation [Fintype B] [Fintype (RelativeWeyl.Weyl T)] :
    Prop :=
  ∀ (J : Finset B) (n : RelativeWeyl.normalizer T),
    QuotientGroup.mk n = longestRep actual J →
      (L (associatedSubset actual J)).map (MulAut.conj (n : G) : G →* G) = L J

end ActualQuotient

end

end Langlands.Group.RelativeWeylIndexing
