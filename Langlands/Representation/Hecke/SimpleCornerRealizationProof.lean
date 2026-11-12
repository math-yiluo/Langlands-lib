import Langlands.Representation.Hecke.SimpleCornerRealizationReduction
import Langlands.Algebra.NonUnitalModuleCornerSimpleInduced
import Langlands.Algebra.NonUnitalModuleCornerSimpleFixedComparison
import Langlands.Representation.Hecke.NondegenerateModuleEquivalenceProof

/-! # Renard III.1.5: realization of simple Hecke corner modules -/

namespace Langlands.Hecke

universe u v

/-- Every simple compact-open Hecke corner module is realized by an irreducible
smooth representation, as in Renard III.1.5 Theorem (iii). -/
theorem simpleCornerModuleRealization : SimpleCornerModuleRealizationStatement.{u, v} :=
  simpleCornerRealization_of_general_theorems
    Algebra.NonUnitalModuleCornerSimpleProof.simpleInducedQuotient
    Algebra.NonUnitalModuleCornerSimpleProof.fixedPartInducedQuotient
    heckeNondegenerateModuleEquivalence

end Langlands.Hecke
