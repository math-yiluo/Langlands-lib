# Tensor product on exact virtual continuous representations

## Meaning and provenance

This is an internal derived construction of tensor product on the exact
Grothendieck groups already defined in `Langlands.VirtualRepresentation.Exact`.
Its inputs are genuine finite-dimensional complex representations of a group
`G`, continuous into the usual finite-dimensional endomorphism topology, with
no restriction on semisimplicity or on the image of the action. The construction
uses the published actual tensor objects, intertwiners and equivalences in
`Langlands.Weil.Representation.SumsTensor` and the continuity proof in
`Langlands.Weil.Representation.OperationClosureProof`. It does not assert a
local-constant identity or an irreducible decomposition. There is no claim that
this quotient construction is quoted verbatim from an external source.

The group needs a `Group` structure and a `TopologicalSpace`; the proofs do not
need continuity of group multiplication. Continuity always has the published
meaning `FiniteRepresentation.IsContinuous` for complex representations.

## Actual exactness

`FiniteRepresentation.isShortExact_tensor_right` and
`FiniteRepresentation.isShortExact_tensor_left` take the published
`IsShortExact f g`: injectivity of the first actual intertwiner, surjectivity of
the second, and equality of its kernel with the first map's range. They prove
these same three conditions for the actual `tensorMap` maps, tensoring with
the identity intertwiner of an arbitrary finite-dimensional complex
representation. The three objects of the sequence and the fixed tensor factor
may have independent carrier universes.

The implementation identifies the underlying linear maps definitionally with
Mathlib's `LinearMap.rTensor` or `LinearMap.lTensor`. Complex vector spaces are
free and hence flat. The corresponding
`Module.Flat.rTensor_preserves_injective_linearMap` /
`lTensor_preserves_injective_linearMap` prove injectivity;
`LinearMap.rTensor_surjective` / `lTensor_surjective` prove surjectivity; and
`Module.Flat.rTensor_exact` / `lTensor_exact`, together with
`LinearMap.exact_iff`, give the range-kernel equality. These are proved Mathlib
results, not extra exactness hypotheses. No equivariant splitting is chosen.
The argument includes the zero vector space.

`FiniteRepresentation.isContinuous_tensor` directly uses
`Weil.OperationClosure.continuous_tensor` with the actual actions.

## Descent and universes

In namespace `Langlands.VirtualRepresentation.ExactGrothendieckGroup`,
`Continuous.{uG, uV} G` abbreviates the existing exact quotient for
`P(A) = A.IsContinuous`, with `G : Type uG` and carriers in `Type uV`.
It is not a new representation lattice or a split quotient.

`continuousTensorClass` first descends actual tensor product to the two genuine
isomorphism-class quotients using `FiniteRepresentation.tensorEquiv` and the
proved continuity closure. For a fixed genuine left class,
`continuousTensorClass_isExactAdditive_right` sends every actual short exact
sequence on the right to the defining exact relation of the target quotient.
The existing `lift` then gives `continuousTensorWithClass`, a linear map on the
right exact group. Its evaluation is
`continuousTensorWithClass_ofClass`.

`continuousTensorWithClass_isExactAdditive` proves exact additivity in the left
class with values in the group of those linear maps. By `hom_ext`, it suffices
to evaluate on each genuine right class. Actual right tensor exactness gives
the required relation there. A second application of `lift` constructs
`continuousTensor`. In each application, the existing universal property kills
the whole integral span `exactRelations`, not merely the displayed relation
generators. Thus both quotient descents are justified.

The resulting map has type

```text
Continuous.{uG, uV} G →ₗ[ℤ]
  Continuous.{uG, uW} G →ₗ[ℤ] Continuous.{uG, max uV uW} G.
```

The tensor carrier really lives in the maximum of the two carrier universes.
Neither source carrier universe is identified with the group universe.
`continuousTensorSame` specializes both factors to `uV`, giving an operation
on a single exact group for arithmetic consumers.

## Evaluation, linearity and degree

`continuousTensor_ofRepresentation` evaluates the constructed bilinear map on
the exact classes of two genuine continuous objects as the exact class of their
actual tensor product, with its proved continuity certificate.
`continuousTensor_add_left`, `continuousTensor_add_right`,
`continuousTensor_smul_left` and `continuousTensor_smul_right` state additivity
and integer-scalar compatibility in both variables. The two `continuousTensor_zero`
lemmas state compatibility with virtual zero.

`degree_compr₂_continuousTensor` is an equality of bilinear maps obtained by
applying `hom_ext` in both variables. On genuine generators it reduces to
`Module.finrank_tensorProduct` and the integer cast of multiplication.
Consequently `degree_continuousTensor` states, for arbitrary virtual classes,

```text
degree (continuousTensor x y) = degree x * degree y.
```

These are the genuine integer degrees of the exact quotient, including negative
and zero degrees. No positive-rank hypothesis is used.
`ofRepresentation_eq_zero_of_rank_zero` uses that a rank-zero complex carrier is
a subsingleton: the two zero maps in the sequence from that object to itself to
itself are short exact. Its exact relation reads `[A] = [A] + [A]`, so `[A] = 0`.
`continuousTensor_rank_zero_left` and `continuousTensor_rank_zero_right` then
show that any genuine rank-zero factor annihilates the tensor product, even
when the other factor is virtual.

## Agreement with character twisting

`FiniteRepresentation.tensorCharacterLineEquiv` constructs a genuine
intertwining equivalence from `tensor A (characterLine χ)` to `twist χ A` in a
single carrier universe. Its underlying linear equivalence is tensoring with
`ULift.moduleEquiv` followed by `TensorProduct.rid`. It sends a pure tensor
`v ⊗ z` to `z.down • v`; the intertwining identity is scalar multiplication and
linearity of the action.

`continuousTensor_characterClass` uses this actual equivalence and `hom_ext` to
prove, for every virtual class `x` and genuine continuous character `χ`,

```text
continuousTensorSame x (characterClass χ) = continuousTwist χ x.
```

The right side is the already published exact twist automorphism from
`ExactTwist`, and the character class is the already published lifted line from
`CharacterLine`. This construction therefore agrees with scalar twisting by a
rank-one continuous character. No ring coherence or determinant formula is
asserted here.

Authorship: Worker 98. All other mathematical dependencies are imported from
the published Library and Mathlib.
