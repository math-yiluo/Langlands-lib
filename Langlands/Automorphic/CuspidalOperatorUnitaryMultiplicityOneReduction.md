# Reduction of actual cuspidal multiplicity one to unitary central characters

Author: Worker 779, Task 7293.

This internal conditional reduction preserves the arbitrary universe `u` and the exact
Library target `Langlands.Automorphic.CuspidalOperatorMultiplicityOneStatement.{u}`.
It retains the unproved proposition
`Langlands.Automorphic.CuspidalOperatorUnitaryMultiplicityOneStatement.{u}`:
equivalent actual cuspidal operator realizations with unitary central characters have
the same underlying subspace of stable automorphic functions. Both realizations carry
the finite, standard compact, and real differential operators used by the unrestricted
target.

The module proves
`cuspidalOperatorUnitaryMultiplicityOneReduction`, whose type is the Prop-valued
`CuspidalOperatorUnitaryMultiplicityOneReductionStatement`: the retained unitary case
implies the exact unrestricted target. The unitary case, and hence the unconditional
multiplicity-one task, remain open.

## Implemented proof

First, `OperatorRealization.Equivalence.hasCentralCharacter` transports any prescribed
central character through a full operator equivalence. For each finite place, the scalar
matrix acts on the source by the corresponding local character value. The equivalence
commutes with that finite action and is linear and surjective, so the same equality
holds on the target. The target's closed central-character subgroup therefore contains
every local finite multiplicative group. It also contains all principal ideles by rational
invariance. The published closed-idele-subgroup density theorem makes it the whole idele
group, giving the central-character identity on actual continuous functions. This argument
requires neither cuspidality nor irreducibility.

Second, `OperatorRealization.Equivalence.heckeDeterminantTwist` sends an equivalence `e`
to `Mχ ∘ e ∘ Mχ⁻¹` between the two actual twisted subspaces, where `Mχ` is multiplication
by `χ(det g)`. The published twist covariance identifies the action of an arbitrary
operator `a` on either twist with the action of
`heckeDeterminantOperatorConjugation n χ a` before multiplication. The original
equivalence commutes with this operator, proving full equivariance of the conjugate.
This retains the shifted differential action required for an arbitrary Hecke character.

Third, `OperatorRealization.heckeDeterminantTwist_injective` reflects equality of actual
subspaces: their underlying submodules are images under the same injective ambient
linear multiplier, and submodule image under an injective linear map is injective.

For the final reduction, the published
`OperatorRealization.existsUnique_hasCentralCharacter` supplies a central character `ω`
of the first irreducible cuspidal realization; transport gives the same `ω` for the
second. Set `μ = unitarizingCharacter r ω`, namely `‖ω‖^(-1/(r+1))`.
The published
`hasUnitaryCentralCharacter_heckeDeterminantTwist_unitarizingCharacter` shows that the
two actual twists have unitary central character `μ^(r+1) * ω`. They are again
irreducible and cuspidal by the existing actual twist construction. Apply the retained
unitary multiplicity-one premise to the conjugated equivalence. Injectivity of the
common ambient multiplier reflects the resulting subspace equality to the original
realizations.

## Provenance and scope

This is an internal derived reduction authorized by the intermediate-results clause of
Task 7293 revision 1. Its construction reuses the normalization already implemented in
`Langlands.Automorphic.CuspidalContragredientExistenceProof` and the actual twists of
`Langlands.Automorphic.HeckeTwist.OperatorTwist`. It makes explicit why the fixed
unitary-central-character setting in Shalika (1974), Theorem 5.5, can serve as a
normalization for the unrestricted operator-realization target.

The reduction supplies no smooth globalization, extension of an operator equivalence
to a full archimedean group action, continuity of cusp Whittaker functionals, or local
Whittaker uniqueness. Those analytic obligations are still needed to prove the retained
unitary premise. In particular, it makes no uniqueness claim for arbitrary algebraic
Whittaker functionals on Harish-Chandra modules. The actual normalization and transport
are proved using the published Library constructions, rather than asserted as consequences
of Shalika's analytic theorem.
