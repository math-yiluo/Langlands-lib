# Tensor unit and extraction of the standard Euler polynomial

This is an internal construction from the existing Weil–Deligne tensor product,
its morphisms, and the correspondence pair-factor definitions. It does not
transcribe an additional theorem from the literature.

For any field, group and norm character, `tensorUnit` is the trivial scalar
representation with zero monodromy. `tensorUnitEquiv` constructs the actual
right unitor from the tensor product with this pair to the original pair. Its
linear map sends `v tensor a` to `a v`. The proof checks the group-intertwining
and monodromy equations on pure tensors; the scalar pair has trivial action and
zero monodromy.

`tensorRightEquiv` tensors an actual pair equivalence in the second argument,
allowing its two carriers and the first carrier to have independent universes.
The underlying linear equivalence is the tensor product of identity with the
supplied equivalence. The existing tensor product of morphisms supplies the
intertwining and monodromy laws. Invariance of the rational L-factor under pair
equivalence then proves `pairLFactor_tensorUnit` and its version for any pair
equivalent to the scalar unit.

For an actual local parameter class `D0` satisfying the existing predicate
`IsRankOneParameterCharacter F 1 D0`, `arithmeticPairLFactor_trivial_right`
identifies the arithmetic factor against `D0` with the reciprocal of
`parameterEulerPolynomial F D`. It chooses a representative of `D`, uses the
representative and actual scalar-pair equivalence supplied for `D0`, and applies
the tensor-unit factor identity. Quotient descent identifies the resulting
Euler polynomial with the class polynomial.

`IsPairLCompatibleAt.standardEulerPolynomial` applies this identity to the
polynomial supplied by pair L-compatibility, for every self-dual measure for the
specified nontrivial additive character. Inversion in the rational-function
field and the injective polynomial inclusion show that the supplied denominator
is exactly `parameterEulerPolynomial F D`. The parameter and automorphic
carrier universes remain independent.

This module does not prove the automorphic maximal-degree criterion or the
spherical spectrum comparison. Those representation-theoretic inputs and the
principal-series conclusion of `FullCorrespondenceUnramifiedStatement` remain
separate obligations.
