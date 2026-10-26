# Horizontal alternating spaces for the actual archimedean pair

This internal construction specializes
`Langlands.HorizontalAlternating` to the concrete reduced and compact
archimedean matrix Lie algebras. It builds the underlying horizontal equivariant
spaces and their coefficient maps. A relative differential and cohomology are
not part of this module.

All declarations are in `Langlands.Global.ArchimedeanGL`. The inputs are a
field `K : Type u` and any natural rank `n`, including zero. No number-field
instance or positive-rank assumption is required for these constructions.
Coefficient modules have independent universes and are complex modules with
additive commutative group structures.

## The actual pair and its actions

The domain is `ReducedComplexLieAlgebra K n`, the complexification of the
kernel of the coordinatewise real trace. At a real place this kernel imposes
trace zero; at a complex place it imposes zero real part of trace, retaining
imaginary scalar directions before complexification. The compact algebra is
`CompactComplexLieAlgebra K n`, the complexification of the real skew-adjoint
matrix Lie algebra. Its existing complex-linear Lie inclusion into the reduced
algebra is `compactToReducedComplex K n`.

`reducedCompactRepresentation K n` bundles the actual
`reducedComplexLieConjugation K n k.val` as a complex representation of
`standardInfiniteCompact K n`. `compactAdjointRepresentation K n` likewise
bundles `compactComplexLieConjugation K n k`. Both use the established
conjugation identity and multiplication laws. Multiplication is in the order
`Ad(k l) X = Ad(k) (Ad(l) X)`. The two `_apply` lemmas identify the bundled
actions with these exact maps.

The group is the full standard compact subgroup, constructed from all real
orthogonal and complex unitary factors. In particular its real orthogonal
factors are not restricted to determinant one or their identity components.
No continuity or differentiability assertion about the coefficient
representation is added.

`compactToReducedIntertwiner K n` bundles the actual compact-to-reduced
inclusion as an intertwiner between the two representations. Its intertwining
law is the established compatibility of compact and reduced conjugation.
`compactToReducedComplex_injective` proves the inclusion is injective: composing
an equality with the reduced inclusion gives equality under the injective
ambient compact inclusion.

`compactInReducedSubmodule K n` is exactly the linear range of
`compactToReducedComplex K n`. Its membership lemma says that `X` belongs if
and only if some `Y : CompactComplexLieAlgebra K n` maps to `X`.
`compactInReducedSubmodule_stable` proves this image is stable under every
element of the full compact group. If `X` is the image of `Y`, the witness for
its translate is `compactComplexLieConjugation K n k Y`; the intertwining
identity verifies that witness.

## Horizontal equivariant spaces

Given any
`ρ : Representation ℂ (standardInfiniteCompact K n) V` and degree `q`,
`horizontalEquivariantSubmodule K n ρ q` is the actual submodule of alternating
maps from `ReducedComplexLieAlgebra K n` to `V` obtained by applying the generic
horizontal construction to `compactInReducedSubmodule K n` and
`reducedCompactRepresentation K n`.

The membership theorem exposes precisely two conditions:

1. For every tuple `x`, index `i`, and compact vector `Y`, if
   `x i = compactToReducedComplex K n Y`, then `f x = 0`.
2. For every element `k` of the full standard compact group and every tuple `x`,
   `f (fun i => reducedComplexLieConjugation K n k.val (x i)) = ρ k (f x)`.

The proof converts range membership to the explicit compact preimage
condition. The second condition is the defining generic equivariance condition
with the actual adjoint representation substituted. No quotient carrier or
unspecified relative Lie algebra replaces these matrix constructions.

## Coefficient maps and degree zero

`horizontalMapCoefficients K n q A` postcomposes with an actual intertwiner
`A` of the full-compact coefficient representations. Its value on a tuple is
`A (f.val x)`. The identity and composition laws are inherited directly from
the generic construction.

`horizontalCoefficientEquiv K n q e` transports these spaces by a coefficient
representation equivalence `e`, using postcomposition by `e` and its inverse.
`horizontalDegreeZeroEquiv K n ρ` gives the linear equivalence

`horizontalEquivariantSubmodule K n ρ 0 ≃ₗ[ℂ] ρ.invariants`.

It is the generic empty-tuple evaluation equivalence: horizontality is vacuous
in degree zero and equivariance says that the coefficient vector is fixed by
every element of the standard compact subgroup. It is an equivalence of
underlying degree-zero spaces, not a computation of zeroth cohomology.

## Provenance and remaining constructions

This source-free internal module combines the actual adjoint equivalences and
inclusion compatibilities in `ArchimedeanRelativeAdjoint`, the actual pair in
`ArchimedeanSplitCenter` and `ArchimedeanCompactLieAlgebra`, and the linear
subspace construction in `Representation.HorizontalAlternating`. It introduces
no new claim of correspondence with an original mathematical source.

The coefficient representation is an explicit input and no coefficient Lie
action is supplied. Compatibility with differentiation, the relative
differential and its stability on these subspaces, its square-zero identity,
cycles, boundaries, quotient cohomology, and a cohomological infinity criterion
remain separate obligations. There is also no identification here of the
matrix compact algebra with a manifold tangent space.
