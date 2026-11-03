# Exact-K0 reduction of contragredient commutation

This module is an internal algebraic reduction for the published general
Aubert operator. It does not prove compatibility of smooth duality with
normalized induction or Jacquet restriction.

`ContragredientGeneratorComparison` states equality of the two actual signed
class sums on every finite-length smooth representation. On the left the
induction–Jacquet functors are applied to its smooth dual; on the right the
smooth dual is applied to each induction–Jacquet term. All classes belong to
the existing exact finite-length Grothendieck group, with its actual short
exact sequence relations. The coefficient is exactly `(-1)^|I|`.

`contragredientCommutation_iff_generatorComparison` proves that this equality
is equivalent to the published `ContragredientCommutationStatement`.
It expands the two linear maps on canonical generators using
`alternatingOperator_ofRepresentation` and
`contragredientK0_ofRepresentation`. The reverse implication uses
`FiniteLengthGrothendieckGroup.hom_ext_object`, which applies to the exact
quotient itself.

`ContragredientTermComparison` is a sufficient additional hypothesis. It
asks for a cardinality-preserving equivalence of the finite-subset indices
and an equality of the corresponding actual classes for every finite-length
representation. It asks for equality in exact K0, not an isomorphism of the
induced representations. The theorem
`ContragredientTermComparison.generatorComparison` rewrites each summand
and uses `Equiv.sum_comp`; `contragredientCommutation_of_termComparison`
then applies the preceding equivalence. Empty index types require no
separate argument.

The extra class comparison is not discharged here and is not added to the
published target. Its representation-theoretic proof remains necessary
before the final closed target can be proved. In particular, finite-length
preservation of the ambient smooth dual supplies the classes but does not
supply the comparison.

Provenance is internal: these are linear-algebraic reductions of the actual
published operator and contragredient constructions. The proof bodies use
only the generator formulas, the exact-K0 extensionality theorem, linear
map identities, finite sums, and proof irrelevance. The imported
`ContragredientTarget` transitively imports `AlternatingOperator`, including
its constructions of exact normalized induction/Jacquet maps and the exact
smooth dual map. No Langlands classification, character independence,
geometric lemma, adjointness, or cuspidal-support theorem is used by these
reduction proofs. This statement is about their declaration dependencies;
the supplied term-comparison hypothesis has no proof in this module.
