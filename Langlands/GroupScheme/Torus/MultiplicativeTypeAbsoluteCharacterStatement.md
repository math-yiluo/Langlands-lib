# Actual absolute-Galois characters: finiteness and continuity

Author: Worker 3483.

These proposition declarations isolate the two assertions needed to bundle
actual characters in the finitely generated discrete absolute-Galois module
category. They assert results about the existing character group and canonical
action. They supply no proofs.

## Exact scope

Let `k : Type u` be any field and `T` an actual commutative group scheme over
`Spec k`. The sole group hypothesis is `IsMultiplicativeType T.toGrp`.
This is the published predicate saying that after some field extension the
group is isomorphic to `D(M)` for a finitely generated abelian group `M`.
The hypothesis supplies neither a chosen splitting model nor a separable or
finite Galois splitting extension.

Write `Ω = SeparableClosure k`, with its existing `k`-algebra structure.
The character group in the statements is exactly

```text
X*(T_Ω) = Hom_CommGroupScheme(Spec Ω)(T_Ω, Gm_Ω).
```

Its addition is the actual pointwise product of characters. These are morphisms
of group schemes on all test schemes, including nonreduced tests.

`MultiplicativeTypeAbsoluteCharacterFiniteStatement.{u}` asserts that this
actual character group is a finitely generated module over `ℤ`.
It does not replace the group by a chosen abstract diagonalizable model.
Finite generation imposes no freeness or torsion-free condition.

`MultiplicativeTypeAbsoluteCharacterSmoothStatement.{u}` asserts `IsSmooth`
of the existing
`characterLattice.galoisRepresentation k (SeparableClosure k) T`.
Here the automorphism group is exactly
`SeparableClosure k ≃ₐ[k] SeparableClosure k`, with Mathlib's Krull topology.
The published definition of `IsSmooth` says that each character is fixed by
an open subgroup of that group. The open subgroup can depend on the character.
The term “smooth” in this assertion describes the representation; it imposes
no smoothness condition on `T`.

The entry proposition `MultiplicativeTypeAbsoluteCharacterStatement.{u}` is
the conjunction of these two universally quantified assertions.
There is no characteristic, connectedness, reducedness or smoothness
hypothesis on `T`, so finite nonsmooth groups of multiplicative type and
their torsion characters are included. All scheme and field types are in
the same arbitrary universe `u`, as in the existing character construction.

## Continuity meaning

The action is the already constructed canonical descent action on actual
characters. No arbitrary action is selected. By the independently published
`Langlands.isSmoothVector_iff_continuous_orbitMap`, the second assertion
is equivalent to continuity of each orbit map after supplying a discrete
topology on the character group. Mathlib's `continuous_prod_of_discrete_right`
then gives joint continuity. No topology on character groups is installed as
a global instance by this statement module.

## Source and proof boundaries

The registered original source is J. S. Milne, *Algebraic Groups* (2017),
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Section 12.g, printed p.239 / PDF p.255, defines the character group over
a separable closure and describes the Krull action and open-subgroup
criterion. Its finite field-of-definition argument gives continuity.
Theorem 12.23, printed p.240 / PDF p.256, gives the finitely generated
continuous integral-module target for groups of multiplicative type.
These declarations isolate its object-membership assertions for the
published actual characters; they do not state the categorical equivalence.
Both original pages and the complete retained official 2017 errata snapshot
were read. No listed correction changes these passages.

The finite-generation assertion still requires a proof that applies to the
published `IsMultiplicativeType` hypothesis. In particular, finite Galois
splitting is a separate existing theorem obligation; it is not assumed here
or inserted into the definition of multiplicative type. The continuity
assertion can use finite fields of definition of actual homomorphisms and
openness of their fixing subgroups. These are proof routes, not proofs in
this module. Constructing the actual functor into the discrete module
category and proving the absolute-Galois anti-equivalence remain subsequent
obligations.
