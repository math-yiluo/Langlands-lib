import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Group.RelativeWeylIndexing
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# General targets for Aubert Corollary 1.10

All representations, exact sequences, coinvariants and K0 maps are actual.
The subgroup families are the standard families at specialization; their
structural realization and the named finite-length/exactness premises remain
separate obligations. This file declares targets, not the corollary's proofs.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Aubert.General

universe uI uG uV

open SmoothRep
open Langlands.Group

section ElementaryPredicates

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- An actual length-two composition series with the indicated irreducible
factors, in either order. No semisimplicity or splitting is assumed. -/
def HasTwoConstituents (A ρplus ρminus : SmoothRep.{0, uG, uV} ℂ G) : Prop :=
  ρplus.IsIrreducible ∧ ρminus.IsIrreducible ∧
    ((∃ (f : ρplus.representation.IntertwiningMap A.representation)
        (g : A.representation.IntertwiningMap ρminus.representation), IsShortExact f g) ∨
     (∃ (f : ρminus.representation.IntertwiningMap A.representation)
        (g : A.representation.IntertwiningMap ρplus.representation), IsShortExact f g))

variable {ι : Type uI} [Fintype ι] [DecidableEq ι]

/-- The source's relative-rank-one condition `J = S \ {α}`. In particular
there is no such `J` when the simple-root type is empty. -/
def IsMaximalStandard (J : Finset ι) : Prop :=
  ∃ α : ι, J = Finset.univ.erase α

end ElementaryPredicates

section LeviCuspidality

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}
variable (P M U : Finset ι → Subgroup G)

/-- Cuspidality in the actual closed Levi `M J`: every proper standard
normalized Jacquet module inside `M J` is a zero object.
The coinvariants are those of the actual subgroup
`(U I).subgroupOf (M J)`. -/
def IsCorollaryLeviCuspidal (J : Finset ι) (hM : IsClosed (M J : Set G))
    (hJ : ∀ I : Finset J, IsSemidirectDecomposition
      ((P (leviIndex J I)).subgroupOf (M J))
      ((M (leviIndex J I)).subgroupOf (M J))
      ((U (leviIndex J I)).subgroupOf (M J)))
    (hU : ∀ I, IsClosed (U I : Set G))
    (σ : SmoothRep.{0, uG, max uG uV} ℂ (M J)) : Prop :=
  letI := hM.locallyCompactSpace
  ∀ I : Finset J, I ≠ Finset.univ →
    IsZero ((jacquetFunctor (hJ I)
      ((hU (leviIndex J I)).preimage continuous_subtype_val)).obj σ)

end LeviCuspidality

section Corollary

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI} [Fintype ι] [DecidableEq ι]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hfl : ∀ I, ParabolicFiniteLength.{uG, max uG uV} (h I) (hU I))
  (hM : ∀ J, IsClosed (M J : Set G))
  (hLevi : ∀ (J : Finset ι) (I : Finset J), IsSemidirectDecomposition
    ((P (leviIndex J I)).subgroupOf (M J))
    ((M (leviIndex J I)).subgroupOf (M J))
    ((U (leviIndex J I)).subgroupOf (M J)))

/-- Corollary 1.10(a), including its source irreducibility hypothesis:
`D_G [i_J σ] = (-1)^|J| [i_J σ]` for irreducible cuspidal `σ` when
`i_J σ` is irreducible. This includes `J = ∅` and the empty simple-root type. -/
def corollary110a : Prop :=
  ∀ (J : Finset ι) (σ : FiniteLengthObject.{0, uG, max uG uV} ℂ (M J)),
    σ.val.IsIrreducible → IsCorollaryLeviCuspidal P M U J (hM J) (hLevi J) hU σ.val →
    ((normalizedInductionFunctor (h J) (hU J)).obj σ.val).IsIrreducible →
      alternatingOperator P M U h hU hfl
        (inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1
          (FiniteLengthGrothendieckGroup.ofObject σ)) =
      ((-1 : ℤ) ^ J.card) •
        inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1
          (FiniteLengthGrothendieckGroup.ofObject σ)

/-- The signed exchange formula in Corollary 1.10(b) for two actual
finite-length constituents. -/
def ConstituentExchange (J : Finset ι)
    (ρplus ρminus : FiniteLengthObject.{0, uG, max uG uV} ℂ G) : Prop :=
  ((-1 : ℤ) ^ J.card) • alternatingOperator P M U h hU hfl
      (FiniteLengthGrothendieckGroup.ofObject ρplus) =
    FiniteLengthGrothendieckGroup.ofObject ρminus ∧
  ((-1 : ℤ) ^ J.card) • alternatingOperator P M U h hU hfl
      (FiniteLengthGrothendieckGroup.ofObject ρminus) =
    FiniteLengthGrothendieckGroup.ofObject ρplus

/-- The length-two representation-theoretic prerequisite cited to Casselman
§7.1 in Aubert's proof. It is separate from the signed-exchange conclusion. -/
def rankOneLengthTwo : Prop :=
  ∀ (J : Finset ι), IsMaximalStandard J →
    ∀ (σ : FiniteLengthObject.{0, uG, max uG uV} ℂ (M J)),
      σ.val.IsIrreducible → IsCorollaryLeviCuspidal P M U J (hM J) (hLevi J) hU σ.val →
      ¬ ((normalizedInductionFunctor (h J) (hU J)).obj σ.val).IsIrreducible →
      ∃ ρplus ρminus : FiniteLengthObject.{0, uG, max uG uV} ℂ G,
        HasTwoConstituents ((normalizedInductionFunctor (h J) (hU J)).obj σ.val)
          ρplus.val ρminus.val

/-- Corollary 1.10(b) at its source scope: reducible induction of an
irreducible cuspidal representation from a maximal standard Levi has two
irreducible composition factors, exchanged by `(-1)^|J| D_G`. -/
def corollary110b : Prop :=
  ∀ (J : Finset ι), IsMaximalStandard J →
    ∀ (σ : FiniteLengthObject.{0, uG, max uG uV} ℂ (M J)),
      σ.val.IsIrreducible → IsCorollaryLeviCuspidal P M U J (hM J) (hLevi J) hU σ.val →
      ¬ ((normalizedInductionFunctor (h J) (hU J)).obj σ.val).IsIrreducible →
      ∃ ρplus ρminus : FiniteLengthObject.{0, uG, max uG uV} ℂ G,
        HasTwoConstituents ((normalizedInductionFunctor (h J) (hU J)).obj σ.val)
          ρplus.val ρminus.val ∧
        ConstituentExchange P M U h hU hfl J ρplus ρminus

section WeylPrerequisites

variable (T : Subgroup G) {C : CoxeterMatrix ι}
  (actual : RelativeWeylIndexing.ActualCoxeterSystem T C)
  [Fintype (RelativeWeyl.Weyl T)]

/-- Reducible maximal-Levi cuspidal induction forces self-association.
This is a representation-theoretic target, not a field of external structural
data. Both the associated subset and every actual longest-representative
lift must preserve the indicated actual Levi. -/
def rankOneSelfAssociation : Prop :=
  ∀ (J : Finset ι), IsMaximalStandard J →
    ∀ (σ : FiniteLengthObject.{0, uG, max uG uV} ℂ (M J)),
      σ.val.IsIrreducible → IsCorollaryLeviCuspidal P M U J (hM J) (hLevi J) hU σ.val →
      ¬ ((normalizedInductionFunctor (h J) (hU J)).obj σ.val).IsIrreducible →
      RelativeWeylIndexing.associatedSubset actual J = J ∧
      ∀ n : RelativeWeyl.normalizer T,
        QuotientGroup.mk n = RelativeWeylIndexing.longestRep actual J →
        ∀ x : G, x ∈ M J ↔ (n : G) * x * (n : G)⁻¹ ∈ M J

/-- The actual normalized Jacquet assertions in Aubert's rank-one proof.
The minus constituent has Jacquet module `Ad(n⁻¹) σ`, with inverse pullback
`x ↦ n x n⁻¹`, and every other proper standard Jacquet module vanishes. -/
def RankOneJacquetPattern (J : Finset ι)
    (σ : SmoothRep.{0, uG, max uG uV} ℂ (M J))
    (ρplus ρminus : SmoothRep.{0, uG, max uG uV} ℂ G)
    (n : RelativeWeyl.normalizer T)
    (hself : ∀ x : G, x ∈ M J ↔ (n : G) * x * (n : G)⁻¹ ∈ M J) : Prop :=
  Nonempty (((jacquetFunctor (h J) (hU J)).obj ρplus) ≅ σ) ∧
  Nonempty (((jacquetFunctor (h J) (hU J)).obj ρminus) ≅
    (conjugationFunctor (n : G)⁻¹ (fun x => by simpa using hself x)).obj σ) ∧
  ∀ K : Finset ι, K ≠ Finset.univ → K ≠ J →
    IsZero ((jacquetFunctor (h K) (hU K)).obj ρplus) ∧
    IsZero ((jacquetFunctor (h K) (hU K)).obj ρminus)

/-- Jacquet prerequisite for Corollary 1.10(b), separate from length two,
self-association and the corollary. The self-association proof supplies the
domain of `Ad(n⁻¹)`; it is not taken as an external structural assertion. -/
def rankOneJacquetModules : Prop :=
  ∀ (J : Finset ι), IsMaximalStandard J →
    ∀ (σ : FiniteLengthObject.{0, uG, max uG uV} ℂ (M J)),
      σ.val.IsIrreducible → IsCorollaryLeviCuspidal P M U J (hM J) (hLevi J) hU σ.val →
      ¬ ((normalizedInductionFunctor (h J) (hU J)).obj σ.val).IsIrreducible →
      ∀ (n : RelativeWeyl.normalizer T),
        QuotientGroup.mk n = RelativeWeylIndexing.longestRep actual J →
        ∀ hself : (∀ x : G, x ∈ M J ↔ (n : G) * x * (n : G)⁻¹ ∈ M J),
        ∃ ρplus ρminus : FiniteLengthObject.{0, uG, max uG uV} ℂ G,
          HasTwoConstituents ((normalizedInductionFunctor (h J) (hU J)).obj σ.val)
            ρplus.val ρminus.val ∧
          RankOneJacquetPattern P M U h hU T J σ.val ρplus.val ρminus.val n hself

end WeylPrerequisites
end Corollary

end Langlands.Aubert.General
