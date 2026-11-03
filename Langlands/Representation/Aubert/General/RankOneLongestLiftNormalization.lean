import Langlands.Representation.Aubert.General.JacquetTarget
import Langlands.Group.RelativeWeylSolomonProof

/-! # Recovering rank-one subset equality from actual Levi normalization -/

noncomputable section

namespace Langlands.Aubert.General

universe uI uG

open Langlands.Group
open RelativeWeylIndexing

variable {G : Type uG} [Group G] {B : Type uI} [Fintype B]
  (M : Finset B → Subgroup G) (T : Subgroup G) {C : CoxeterMatrix B}
  (actual : ActualCoxeterSystem T C) [Fintype (RelativeWeyl.Weyl T)]

/-- Some actual normalizer lift of the specified longest quotient class
normalizes the indicated actual Levi. -/
def HasNormalizingLongestLift (J : Finset B) : Prop :=
  ∃ n : RelativeWeyl.normalizer T,
    QuotientGroup.mk n = longestRep actual J ∧
    ∀ x : G, x ∈ M J ↔ (n : G) * x * (n : G)⁻¹ ∈ M J

omit [Fintype (RelativeWeyl.Weyl T)] in
/-- Actual Levi Weyl identification makes the standard Levi family injective
in its literal simple-root subsets. -/
theorem leviFamily_injective_of_actualLeviWeylIdentification
    (hIdent : actualLeviWeylIdentification T M actual) : Function.Injective M := by
  intro I J hIJ
  apply standardSubgroup_injective actual
  rw [← hIdent I, ← hIdent J]
  exact congrArg (fun H : Subgroup G => (RelativeWeyl.inclusion T H).range) hIJ

/-- Normalization by one specified longest lift forces the associated subset
to equal the original subset. -/
theorem associatedSubset_eq_of_longestLift_normalizes
    (hIdent : actualLeviWeylIdentification T M actual)
    (hAssociated : actualAssociatedLeviConjugation T M actual)
    (J : Finset B) (n : RelativeWeyl.normalizer T)
    (hn : QuotientGroup.mk n = longestRep actual J)
    (hNorm : ∀ x : G, x ∈ M J ↔ (n : G) * x * (n : G)⁻¹ ∈ M J) :
    associatedSubset actual J = J := by
  apply leviFamily_injective_of_actualLeviWeylIdentification M T actual hIdent
  have hmem := conjugationMembership_of_map_eq (n : G) (hAssociated J n hn)
  ext x
  have hx : (n : G) * x * (n : G)⁻¹ ∈ M J ↔
      x ∈ M (associatedSubset actual J) := by
    simpa [mul_assoc] using hmem ((n : G) * x * (n : G)⁻¹)
  exact hx.symm.trans (hNorm x).symm

/-- With the actual Levi Weyl and conjugation comparisons, normalization by
any specified longest lift is equivalent to the associated-subset equality. -/
theorem longestLift_normalization_iff_associatedSubset_eq
    (hIdent : actualLeviWeylIdentification T M actual)
    (hAssociated : actualAssociatedLeviConjugation T M actual)
    (J : Finset B) (n : RelativeWeyl.normalizer T)
    (hn : QuotientGroup.mk n = longestRep actual J) :
    (∀ x : G, x ∈ M J ↔ (n : G) * x * (n : G)⁻¹ ∈ M J) ↔
      associatedSubset actual J = J := by
  constructor
  · exact associatedSubset_eq_of_longestLift_normalizes
      M T actual hIdent hAssociated J n hn
  · intro hself x
    have hImage := hAssociated J n hn
    rw [hself] at hImage
    have hmem := conjugationMembership_of_map_eq (n : G) hImage
    simpa [mul_assoc] using (hmem ((n : G) * x * (n : G)⁻¹)).symm

/-- Existence of one normalizing longest lift is equivalent to the literal
associated-subset equality; the latter gives normalization for every lift. -/
theorem hasNormalizingLongestLift_iff_associatedSubset_eq
    (hIdent : actualLeviWeylIdentification T M actual)
    (hAssociated : actualAssociatedLeviConjugation T M actual) (J : Finset B) :
    HasNormalizingLongestLift M T actual J ↔ associatedSubset actual J = J := by
  constructor
  · rintro ⟨n, hn, hNorm⟩
    exact associatedSubset_eq_of_longestLift_normalizes
      M T actual hIdent hAssociated J n hn hNorm
  · intro hself
    obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective (longestRep actual J)
    exact ⟨n, hn, (longestLift_normalization_iff_associatedSubset_eq
      M T actual hIdent hAssociated J n hn).mpr hself⟩

end Langlands.Aubert.General
