import Langlands.Algebra.NondegenerateModuleAbelianProof
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-! The filtered-colimit exactness assertion of Renard I.6. -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra.NondegenerateModuleFilteredColimitsStatements

universe uA uI uM

/-- Filtered colimits exist and satisfy Mathlib's exactness axiom. -/
@[pp_with_univ]
def MathlibAB5Statement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
    letI := NondegenerateModuleCat.abelian.{uA, max uI uM} A hA
    ∃ hc : HasFilteredColimitsOfSize.{uI, uI}
        (NondegenerateModuleCat.{uA, max uI uM} A),
      letI := hc
      Nonempty (AB5OfSize.{uI, uI} (NondegenerateModuleCat.{uA, max uI uM} A))

/-- Pointwise short exact filtered systems remain short exact after colimits. -/
@[pp_with_univ]
def ShortExactColimitsStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
    letI := NondegenerateModuleCat.abelian.{uA, max uI uM} A hA
    ∃ hc : HasFilteredColimitsOfSize.{uI, uI}
        (NondegenerateModuleCat.{uA, max uI uM} A),
      letI := hc
      ∀ (J : Type uI) [Category.{uI} J] [IsFiltered J]
          (S : ShortComplex (J ⥤ NondegenerateModuleCat.{uA, max uI uM} A)),
        (∀ j : J,
          (S.map ((evaluation J (NondegenerateModuleCat A)).obj j)).ShortExact) →
        (S.map (colim (J := J) (C := NondegenerateModuleCat A))).ShortExact

/-- Both formulations of the final exactness conclusion of Renard I.6. -/
@[pp_with_univ]
def FilteredColimitAssertions : Prop :=
  MathlibAB5Statement.{uA, uI, uM} ∧ ShortExactColimitsStatement.{uA, uI, uM}

example : Prop := MathlibAB5Statement.{uA, uI, uM}
example : Prop := ShortExactColimitsStatement.{uA, uI, uM}
example : Prop := FilteredColimitAssertions.{uA, uI, uM}

example : Prop := FilteredColimitAssertions.{0, 1, 2}
example : Prop := FilteredColimitAssertions.{0, 2, 1}
example : Prop := FilteredColimitAssertions.{1, 0, 2}
example : Prop := FilteredColimitAssertions.{1, 2, 0}
example : Prop := FilteredColimitAssertions.{2, 0, 1}
example : Prop := FilteredColimitAssertions.{2, 1, 0}

example : FilteredColimitAssertions.{uA, uI, uM} =
    (MathlibAB5Statement.{uA, uI, uM} ∧ ShortExactColimitsStatement.{uA, uI, uM}) := rfl

end Langlands.Algebra.NondegenerateModuleFilteredColimitsStatements
