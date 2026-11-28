import Langlands.TraceFormula.GroupSchemeCuspidalIsotypicTraceFactorizationStatement
import Langlands.TraceFormula.GroupSchemeCuspidalLocalOccurrenceProof
import Langlands.TraceFormula.IsotypicTrace.CuspidalOccurrenceReduction

/-!
# Proof of the isotypic local trace factorization on an irreducible cuspidal summand

`groupSchemeCuspidalIsotypicTraceFactorization` proves
`GroupSchemeCuspidalIsotypicTraceFactorizationStatement`. For an irreducible closed invariant
summand `P` of the group-scheme cuspidal space and a finite place `v`,
`groupSchemeCuspidalLocalOccurrence` supplies an irreducible admissible representation `ρ` of
`G(F_v)` on a `Type u` carrier with a nonzero `G(F_v)`-equivariant linear map into `P`. The
per-summand reduction
`IsotypicTrace.cuspidalIsotypicTraceFactorization_of_exists_occurrence` turns this occurrence
into the realization, isotypy and untwisted and twisted trace factorization clauses for the
same `ρ`.
-/

universe u

namespace Langlands.TraceFormula

/-- **Isotypic local trace factorization on an irreducible cuspidal summand.** The local
occurrence of `groupSchemeCuspidalLocalOccurrence` together with the per-summand reduction
`IsotypicTrace.cuspidalIsotypicTraceFactorization_of_exists_occurrence` proves
`GroupSchemeCuspidalIsotypicTraceFactorizationStatement`. -/
theorem groupSchemeCuspidalIsotypicTraceFactorization :
    GroupSchemeCuspidalIsotypicTraceFactorizationStatement.{u} := by
  intro F _ _ G _ _ hPD hG T i hi _ I _ e hc _ v _ _ _ _ μv _ ν _ S πc P _ hP0 hPinv hPirr
  exact IsotypicTrace.cuspidalIsotypicTraceFactorization_of_exists_occurrence F G v hPD hG T i
    hi I e hc μv ν P hPinv hPirr
    (groupSchemeCuspidalLocalOccurrence F G hPD hG T i hi I e hc v P hP0 hPinv hPirr)

end Langlands.TraceFormula
