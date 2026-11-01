import Langlands.Algebra.NondegenerateModuleAbelianProof
import Langlands.CategoryTheory.RenardCompletenessLimitsStatements

/-! The completeness and cocompleteness assertions of Renard I.6. -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra.NondegenerateModuleCompletenessStatements

universe uA uI uM

/-- All index-sized products exist in the actual nondegenerate category. -/
@[pp_with_univ]
def CompleteStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
    letI := NondegenerateModuleCat.abelian.{uA, max uI uM} A hA
    Langlands.Renard.IsSourceComplete.{uI}
      (NondegenerateModuleCat.{uA, max uI uM} A)

/-- All index-sized coproducts exist in the actual nondegenerate category. -/
@[pp_with_univ]
def CocompleteStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
    letI := NondegenerateModuleCat.abelian.{uA, max uI uM} A hA
    Langlands.Renard.IsSourceCocomplete.{uI}
      (NondegenerateModuleCat.{uA, max uI uM} A)

/-- All diagrams with objects and arrows of index size have actual limits. -/
@[pp_with_univ]
def AllLimitsStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (_hA : IsIdempotented A),
    HasLimitsOfSize.{uI, uI} (NondegenerateModuleCat.{uA, max uI uM} A)

/-- All diagrams with objects and arrows of index size have actual colimits. -/
@[pp_with_univ]
def AllColimitsStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (_hA : IsIdempotented A),
    HasColimitsOfSize.{uI, uI} (NondegenerateModuleCat.{uA, max uI uM} A)

/-- The first assertion of the I.6 proposition, with its all-diagram meaning. -/
@[pp_with_univ]
def CompletenessAssertions : Prop :=
  CompleteStatement.{uA, uI, uM} ∧ CocompleteStatement.{uA, uI, uM} ∧
    AllLimitsStatement.{uA, uI, uM} ∧ AllColimitsStatement.{uA, uI, uM}

/-! Complete closed interfaces retain three independent universe parameters. -/

example : Prop := CompleteStatement.{uA, uI, uM}
example : Prop := CocompleteStatement.{uA, uI, uM}
example : Prop := AllLimitsStatement.{uA, uI, uM}
example : Prop := AllColimitsStatement.{uA, uI, uM}
example : Prop := CompletenessAssertions.{uA, uI, uM}
example : Prop := CompletenessAssertions.{0, 1, 2}
example : Prop := CompletenessAssertions.{0, 2, 1}
example : Prop := CompletenessAssertions.{1, 0, 2}
example : Prop := CompletenessAssertions.{1, 2, 0}
example : Prop := CompletenessAssertions.{2, 0, 1}
example : Prop := CompletenessAssertions.{2, 1, 0}

/-- The source completeness target concludes actual product existence. -/
example : CompleteStatement.{uA, uI, uM} ↔
    (∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
      letI := NondegenerateModuleCat.abelian.{uA, max uI uM} A hA
      HasProducts.{uI} (NondegenerateModuleCat.{uA, max uI uM} A)) := Iff.rfl

/-- The source cocompleteness target concludes actual coproduct existence. -/
example : CocompleteStatement.{uA, uI, uM} ↔
    (∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
      letI := NondegenerateModuleCat.abelian.{uA, max uI uM} A hA
      HasCoproducts.{uI} (NondegenerateModuleCat.{uA, max uI uM} A)) := Iff.rfl

/-- The limit target has no assumed completeness or limit structure. -/
example : AllLimitsStatement.{uA, uI, uM} ↔
    (∀ (A : Type uA) [NonUnitalRing A] (_hA : IsIdempotented A),
      HasLimitsOfSize.{uI, uI}
        (NondegenerateModuleCat.{uA, max uI uM} A)) := Iff.rfl

/-- The colimit target has no assumed cocompleteness or colimit structure. -/
example : AllColimitsStatement.{uA, uI, uM} ↔
    (∀ (A : Type uA) [NonUnitalRing A] (_hA : IsIdempotented A),
      HasColimitsOfSize.{uI, uI}
        (NondegenerateModuleCat.{uA, max uI uM} A)) := Iff.rfl

example : CompletenessAssertions.{uA, uI, uM} =
    (CompleteStatement.{uA, uI, uM} ∧ CocompleteStatement.{uA, uI, uM} ∧
      AllLimitsStatement.{uA, uI, uM} ∧ AllColimitsStatement.{uA, uI, uM}) := rfl

example : CompletenessAssertions.{0, 1, 0} =
    (CompleteStatement.{0, 1, 0} ∧ CocompleteStatement.{0, 1, 0} ∧
      AllLimitsStatement.{0, 1, 0} ∧ AllColimitsStatement.{0, 1, 0}) := rfl

example : CompletenessAssertions.{1, 0, 0} =
    (CompleteStatement.{1, 0, 0} ∧ CocompleteStatement.{1, 0, 0} ∧
      AllLimitsStatement.{1, 0, 0} ∧ AllColimitsStatement.{1, 0, 0}) := rfl

end Langlands.Algebra.NondegenerateModuleCompletenessStatements
