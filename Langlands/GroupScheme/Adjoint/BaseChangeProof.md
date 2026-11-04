# Field base change of actual adjoint quotients

Authors: Workers 1366 and 1490. Worker 1490 supplied the assembly draft;
Worker 1366 completed it using the published connected-reductivity theorem.

The theorem `Langlands.GroupScheme.adjointQuotientBaseChangeStatement`
proves exactly the published proposition
`Langlands.GroupScheme.AdjointQuotientBaseChangeStatement.{u}` from
`Langlands.GroupScheme.Adjoint.BaseChangeStatement`.

For arbitrary fields `k K : Type u` with `Algebra k K`, group schemes `G A`
over `Spec k`, and a homomorphism `q : G ⟶ A`, the sole hypothesis is
`IsAdjointQuotient q`. The conclusion is
`IsAdjointQuotient ((GroupScheme.baseChange (algebraBaseMap k K)).map q)`,
with every field of the existing predicate. The base change is the actual
categorical pullback.

## Implemented proof

Apply the unconditional `connectedReductiveFieldExtensionStatement` from
`Langlands.GroupScheme.Reductive.FieldExtensionProof` to the original source
and to the original adjoint target. The latter is connected reductive through
its semisimple field. The published `HasFiniteCenter.baseChange` from
`Langlands.GroupScheme.Reductive.FiniteCenterBaseChange` transports the target's
finite full centre. The theorem `center_eq_bot_baseChange` from
`Langlands.GroupScheme.Adjoint.GeometricBaseChange` transports triviality of
that full centre. These components give semisimplicity and adjointness of the
base-changed target using their existing definitions.

The underlying map of the actual group-scheme pullback is the map of
`Over.pullback`. Mathlib's `MorphismProperty.overPullbackMap` transports flatness,
surjectivity and local finite presentation separately from the corresponding
fields of the original quotient. These properties are installed as local
instances for the pulled-back homomorphism.

The published `kernelCenter_baseChange` identifies its actual pullback kernel
with the full scheme-theoretic centre: the kernel inclusion is closed and its
range functor equals the entire centre functor on all tests over `Spec K`.
Finally, `IsAdjointQuotient.of_fppf` from
`Langlands.GroupScheme.Adjoint.QuotientDescent` assembles the conclusion.
Its fppf descent construction supplies unique factorizations for every
centre-invariant morphism to every `Y : Over (Spec K)` and every homomorphism
killing the centre to every group scheme over `Spec K`. Neither target needs
to descend from `k`. The group structure on a descended homomorphism is proved
by cancellation after the covering map and its product.

All fields, schemes and tests remain at arbitrary universe `u`. There is no
restriction on characteristic, perfection, separability or transcendence of the
field extension. The full centre retains its possibly nonreduced structure.

## Provenance and source correspondence

This proof is an internal combination of the imported, proved Library APIs.
It introduces no external source assertion or additional premise. The target
statement's paired Markdown records its source correspondence with Milne,
*Algebraic Groups* (2017), Corollary 17.62 and Remark 17.63, Propositions 19.5
and 19.13, and Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition
(2015), A.1.8–A.1.12. The present implementation assembles the precise
categorical statement from the published preservation and descent results;
it does not claim that one source passage states this exact packaging.

The connected-reductivity proof and its source route are documented in
`Reductive/FieldExtensionProof.md`. The finite-centre and actual-kernel
transport arguments are documented in `Reductive/FiniteCenterBaseChange.md`
and `Adjoint/GeometricBaseChange.md`. The fppf descent mechanism, its
correspondence with CGP A.1.11–A.1.12, and its arbitrary-target scope are
documented in `Adjoint/QuotientDescent.md`. This module proves preservation
of a supplied adjoint quotient; it asserts no existence of such a quotient.
