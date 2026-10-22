# Actual ambient adelic function representations

This module constructs complex vector spaces of actual functions on
`Global.AdelicGL K n`, for a number field `K : Type u`. It uses Mathlib
`Representation.coindV` and `Representation.coind` of the trivial
one-dimensional representation along the rational diagonal map.
Consequently the carrier of `RationalInvariantFunctions` is exactly the
functions satisfying

`f (rational γ * x) = f x`.

The right action is `R(g) f(x) = f(x * g)`, with its representation laws
supplied by Mathlib coinduction. No space of representation classes is
substituted for this concrete realization, and the function carrier is not
required to have finite dimension.

`continuousSubrepresentation` cuts out continuous functions. Right translations
preserve it by continuity of multiplication. `ContinuousRationalFunctions`
has its actual linear structure and right action.
`ContinuousRationalFunctions.toContinuousMap` is a proved injective linear
map into continuous functions on the actual adelic group.
The carrier is given the topology induced by this map from the compact-open
topology on continuous functions. The map is a proved topological embedding,
and every fixed right translation is proved continuous. Joint continuity of
the group action is not asserted here.

For an actual continuous complex quasi-character of the idele class group,
`centralCharacterSubrepresentation` imposes

`f (scalar z * x) = χ([z]) * f x`.

The quotient class `[z]` is the actual quotient by principal ideles; no arbitrary
central character values are introduced. Closure under addition, scalar
multiplication and right translation is proved. `scalar_rightAction` proves
that the right representation acts by the same scalar character, using
commutation of scalar matrices. The character need not be unitary.
Its pullback to ideles is continuous and is proved trivial on principal ideles.

For a subgroup `L` of the finite adelic group, `levelSubmodule` is the actual
submodule of `L`-fixed vectors under the finite-factor inclusion.
`HasFiniteLevel` explicitly requires `L` to be compact and open.
`infiniteOrbitSpan` is the span of the actual right translates by a specified
infinite-factor subgroup. `IsInfiniteFinite` states that this span is finite
dimensional over the complex numbers. It does not assert that the supplied
subgroup is maximal compact. The eventual automorphic definition must select
an actual maximal compact subgroup and use the predicate for that subgroup.

The exact source is A. Borel and H. Jacquet, “Automorphic forms and automorphic
representations,” *Automorphic Forms, Representations and L-Functions*,
Proc. Sympos. Pure Math. 33, part 1 (1979), pp. 189–202:

- §1.5(1), p. 190, explains compact-subgroup finiteness by the finite-dimensional
  span of right translates.
- §3.2 and §4.1–4.3, pp. 194–195, supply right translation, rational invariance,
  finite-level invariance and the central-character transformation rule.
- §4.6, pp. 196–197, distinguishes the Hecke-algebra representation of
  automorphic forms from a representation of the full adelic group.

The retained original is `Part I.pdf` in the Borel–Casselman Corvallis folder;
these pages are one-based PDF pages 185 and 189–192. The complete article,
PDF pages 184–197, was read. The submodule and action constructions here are
derived implementation prerequisites for those definitions.

These ambient functions are **not yet automorphic forms**. Smoothness at
infinity, finiteness for the center of the universal enveloping algebra,
growth, and cuspidal quotient integrals remain separate implementation work.
No equivalence between these analytic conditions and admissibility, no
automorphic existence theorem, and no spectral decomposition is assumed.
In particular, the full right action on the ambient space does not assert
that the space of compact-finite automorphic forms is invariant under every
archimedean group translation.
