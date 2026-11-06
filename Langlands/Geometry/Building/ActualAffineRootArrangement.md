# Algebraic laws for the actual affine-root arrangement

The linear map `rootDerivativeCoordinates i` sends a reduced translation
`v : TranslationSpace i` to the function on actual relative roots given by

```text
a ↦ rootForm i a v.
```

It is defined for any field in arbitrary universe `u`, any commutative group
scheme `S`, and any homomorphism `i : S → G` into an affine group scheme.
No monomorphism, valuation or split-torus premise is needed for the coordinate
construction and its injectivity.

For supplied `B : ValuationBuildingData G`, the module derives four of the
five laws of `AffineRootSystem.IsLocallyFiniteReflectionArrangement` for
the existing ordinary affine-root set `B.affineRoots`.

| Law | Additional premise |
| --- | --- |
| Finitely many derivative roots | None |
| Derivative roots span the full real dual of `TranslationSpace B.i` | `RelativeRoot.HasOppositeFactorPairs B.i` |
| Every ordinary affine root is nonconstant | The same opposite-pair-existence premise |
| Every ordinary affine root has a coroot preserving the ordinary roots | The same opposite-pair-existence premise |

The final theorem
`ValuationBuildingData.isLocallyFiniteReflectionArrangement_of_oppositePairs`
assembles the local-arrangement predicate from the opposite-pair premise and
the sole remaining explicit condition:

```text
∀ x bound, {ψ | ψ ∈ B.affineRoots ∧ |ψ x| ≤ bound ψ.linear}.Finite.
```

Here `bound` is any real-valued function on the dual translation space.
This bounded-finiteness condition is retained; the module does not prove it
for arbitrary supplied data.

## Implemented proof

The translation space is the real cocharacter space modulo the common
annihilator of all relative roots. Thus a translation on which every
`rootForm` vanishes is zero, by the quotient's zero criterion and
`mem_rootAnnihilator`. Applying this to `v - w` proves injectivity of
`rootDerivativeCoordinates`. The helper `eq_zero_of_rootForm_eq_zero` is
also used in the spanning proof.

For finiteness of the derivative roots, smoothness is supplied by
`B.isConnectedReductive.smooth`. The actual split torus then has finitely
many actual relative roots by the published root-finiteness theorem.
Every derivative of an ordinary affine root is `rootForm B.i a` for one
of those roots, directly from the definition of `affineRoots`.

For coroot existence, an ordinary affine root is extended, and the published
identity `B.reflectionAffineRoots_eq` realizes it as the valuation functional
of a nonidentity actual root point. The existence premise provides an
actual opposite pair. The published theorem
`B.isCoroot_reflectionCoroot_without_apartment_axioms` supplies its actual
coroot with reflection stability of ordinary affine roots. Since its value
under the derivative is `2`, that derivative cannot be zero.

For spanning, the split torus has finite-dimensional real cocharacter space
by `IsSplitTorus.finite_realCocharacterSpace`. Its reduced quotient is therefore
finite dimensional. Mathlib's `Submodule.span_eq_top_of_ne_zero` reduces the
claim to separating every nonzero translation by an ordinary derivative.
The quotient-coordinate lemma supplies a relative root `a` whose form is
nonzero on that translation. V0 provides a finite value of the `a`-valuation
at an apartment point, and `affineFunctional_mem_extendedAffineRoots` realizes
it as an extended root with derivative `rootForm B.i a`. The hF-derived AS4
theorem `B.affineRoot_mem_or_two_smul_mem_of_oppositePairs` makes this root
or its double ordinary. Its derivative remains nonzero on the translation,
because multiplication by `2` is nonzero over the reals.

No positive-rank or nonempty-root premise is used: the quotient-coordinate
argument also covers the empty relative-root set. The final arrangement
theorem simply fills the four proved fields and retains bounded finiteness
as its fifth field.

## Provenance and scope

This is an internal construction from the existing root-annihilator quotient,
actual relative-root finiteness, ordinary and extended affine-root definitions,
actual opposite-pair coroots and the hF-derived AS4 adapter. Its spanning
argument uses Mathlib's dual-separation theorem. No new external source
assertion is made.

Opposite-pair existence and bounded finiteness remain explicit. No full
apartment-axiom package, AS5 or simple-connectedness premise is used. Full
simply connected normalizer generation is not established, and this unit
does not prove `SimplyConnectedFacetFixingStatement`.
