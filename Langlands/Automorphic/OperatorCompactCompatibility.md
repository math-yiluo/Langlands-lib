# Compact compatibility on actual automorphic realizations

This internal construction applies to an arbitrary number field `F : Type u`,
every natural rank `n`, and actual operator realizations `S` and `T`. All
linear maps have complex coefficients. The carrier `S.Space` remains its
concrete subspace of `StableAutomorphicFunctions F n`. The compact group is
the entire `standardInfiniteCompact F n`, including all components.

Write `R(k)` for `S.compactRepresentation k`, `D(a)` for
`S.envelopingAction a`, and `P(d)` for `S.finiteRepresentation d`.
These are the existing restricted operators, with positive right
translation on functions. The definitions and identities in this module
use those actual operators throughout.

## Covariance on the function spaces

`finiteSmoothRightAction_envelopingAction` proves, for every
`g : InfiniteAdelicGL F n`, that right translation by `ofInfinite g`
intertwines the genuine differential action with
`ArchimedeanGL.envelopingConjugation F n g`. The proof applies injectivity
of the complete family of finite smooth slices. On each slice the two
published slice formulas reduce the identity to
`ArchimedeanGL.envelopingRightCovariance`.

`stableAutomorphicCompactAction_envelopingAction` restricts this identity
to the stable automorphic core and the standard compact group. Equality
of the underlying finite-smooth functions proves equality in the subtype.
The core's previously constructed invariant actions supply the restrictions.

## Realization and finiteness

`OperatorRealization.compactContinuousInclusion` bundles the existing
`S.toContinuous` as an intertwiner for compact translation. It is
injective by `S.toContinuous_injective`. The intertwining equation holds
because both actions are restrictions of the same right translation.

`compactRepresentation_isFiniteVector` proves finite dimensionality over
the complex numbers of the compact orbit span of each realized vector.
Its image in forms satisfies the existing automorphic membership
predicate, which includes compact finiteness. The proof reflects that
condition through the injective continuous-function intertwiner using
`FiniteVectors.isFiniteVector_map_iff`.

`finiteRepresentation_compactRepresentation` proves `P(d) R(k) = R(k) P(d)`
pointwise. Injectivity of `S.toContinuous` reduces it to the published
`finiteTranslateIntertwiner` equation.

## Invertible compact operators and endomorphism conjugation

`compactLinearEquiv k` is the invertible linear map supplied by the group
representation. Its application is `R(k)` and its inverse applies `R(k⁻¹)`,
as the two application lemmas record. `compactFiniteEquivalence k`
uses finite/compact commutation to make this same map an equivalence of
the finite adelic representation with itself.

`compactEndConjugation k` is the complex algebra automorphism of the full
endomorphism algebra `Module.End ℂ S.Space` given by

`A ↦ R(k) ∘ A ∘ R(k⁻¹)`.

It is constructed with Mathlib's `LinearEquiv.conjAlgEquiv`; the
application lemma identifies its value on every vector. Its three
compatibility lemmas say:

- It fixes each finite translation operator `P(d)`.
- It sends `D(a)` to
  `D(ArchimedeanGL.envelopingConjugation F n k.val a)`.
- It sends the actual complex Lie operator at `X` to the operator at
  `ArchimedeanGL.complexLieConjugation F n k.val X`.

The pointwise enveloping covariance
`compactRepresentation_envelopingAction` descends from the core through
`S.inclusion_injective`. The corresponding complex Lie covariance
specializes to the canonical enveloping generator and uses the published
generator-conjugation formula. For endomorphism conjugation, the proofs
apply finite commutation or enveloping covariance to `R(k⁻¹) f` and then
cancel the inverse compact translation. The Lie formula again specializes
the enveloping formula to a generator.

`Intertwiner.compactRestriction` and `Equivalence.compactRestriction`
retain the underlying linear map and linear equivalence of a full
operator intertwiner or equivalence. Their compact intertwining equation
is its full equation specialized to the concrete compact operator.

## Provenance and scope

The provenance is internal restriction and composition of the published
`OperatorLieAction`, `OperatorRealization`, `OperatorEquivalence`,
`OperatorCore`, `ArchimedeanCovarianceProof`, and `ArchimedeanAdjoint`
constructions, together with Mathlib's conversion from invertible
endomorphisms to linear equivalences and its endomorphism conjugation.
No new assertion from original literature is claimed.

The covariance identities are proved from the published smooth covariance;
no covariance hypothesis is added. Compact finiteness here is algebraic
finite dimensionality of each orbit span. This module adds no topology on
`S.Space`, differentiability of its compact representation, or identification
of its compact Lie action with the derivative of that representation.
That analytic identification remains a separate obligation. It also does
not prove differential preservation on the full automorphic-form space,
equality of that space with the stable core, existence of nonzero
realizations, or a cohomological infinity condition.
