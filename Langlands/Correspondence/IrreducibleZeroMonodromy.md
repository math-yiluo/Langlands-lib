# Zero-monodromy parameters of continuous irreducible Weil classes

Authors: Worker 1684 and Worker 422.

This module supplies the parameter-domain bridge used by the induction in
Henniart 2002, §3.4 (printed p.598). It uses the actual local Weil group and
keeps the field and representation-carrier universes independent.

`zeroMonodromyParameter` assigns to every rank-indexed continuous irreducible
Weil class the unique Frobenius-semisimple parameter class of the same rank
with that Weil action and zero monodromy. Existence is proved without further
hypotheses; the definition then uses classical choice, and uniqueness makes
the result independent of all choices.

The existence argument first proves semisimplicity of every operator in a
finite-image complex representation: the operator satisfies `X^m - 1` for a
positive integer `m`, and this polynomial is separable in characteristic zero.
The published `localWeilIrreducibleReductionFor` expresses a continuous
irreducible Weil representation as an unramified scalar twist of a finite-image
representation. Semisimplicity is preserved by the scalar twist and the
intertwining equivalence. The published `localWeilContinuity` gives open inertia
kernel, so its zero-monodromy pair satisfies both actual parameter conditions.

`exists_zeroMonodromyParameter` chooses a representative of the irreducible
Weil class, applies this domain result, and places the resulting object in the
restricted isomorphism quotient. Zero monodromy retains the original vector
space, so the rank certificate is inherited directly.

The imported `ZeroMonodromyExtension` module supplies
`parameterForget_injective` and `IsZeroMonodromyOf.unique`. Its restricted
parameter quotient and unrestricted pair quotient use the same isomorphism
relation, and an intertwiner of two Weil representations also intertwines
their zero monodromy maps. These facts make the zero-monodromy parameter class
unique. This module imports those helpers instead of defining copies.

`zeroMonodromyParameter_spec` and `isZeroMonodromyOf_iff_eq` record the
specification and uniqueness of the chosen parameter.
`parameterForget_zeroMonodromyParameter` identifies its underlying pair
class with the existing `weilPairClass` used by arithmetic factors.
The imported `ExtendsSupercuspidal.apply_of_zeroMonodromy` makes the
existential extension predicate pointwise by identifying its witness with any supplied
zero-monodromy parameter. Its automorphic carrier universe remains independent
of both the field and parameter-carrier universes.

These are internal consequences of the published actual-group reduction,
continuity, and class-space definitions. Worker 1684 wrote the semisimplicity,
existence, and canonical-class bridge. The forgetful injectivity, uniqueness,
and pointwise extension arguments originated in Worker 422's zero-monodromy
draft and are now imported from `ZeroMonodromyExtension`.
The module does not prove the full correspondence extension or a factor
comparison.

Contextual source: Henniart, *Une caractérisation de la correspondance de Langlands locale
pour GL(n)* (2002), §§1.1, 3.1 and 3.4, printed pp.588, 597–598, registered as
`henniart-2002-characterization`, SHA256
`40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
This citation motivates the use of zero-monodromy classes in the induction;
the Lean argument is the internal construction described above.
