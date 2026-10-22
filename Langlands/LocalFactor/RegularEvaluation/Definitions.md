# Algebraic reciprocal evaluation on a regular domain

This internal interface abstracts the denominator evaluation already used by
the Euler, reciprocal-entire, and p-adic abelian local-factor constructions.
It introduces no new model of rational functions or meromorphic germs.

For an arbitrary function `denominator : X → K`, `Point denominator` is an
abbreviation for Mathlib's `Function.support denominator` as a subtype. Thus
its elements are exactly inputs `x` with `denominator x ≠ 0`. This part only
requires a zero on `K`. For a field `K`, `value denominator x` is the inverse
of `Units.mk0 (denominator x.val) x.property`. Its underlying scalar is exactly
the reciprocal of the denominator. A nonzero certificate is required to call
the evaluator; the interface supplies no value at a zero.

`mapInput denominator input` handles substitution of a function `input : Y → X`.
Its domain is the support of the composite denominator, and its result has
underlying input `input y.val`. Evaluation before and after this substitution
is definitionally identical. The construction does not assert that substitution
is invertible or that a spectral parameter is identical to a polynomial variable.
The three carrier universes are independent.

The implementation reuses `Function.support` from
`Mathlib.Algebra.Notation.Support` and `Units.mk0` from
`Mathlib.Algebra.GroupWithZero.Units.Basic`, at pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. There is no replacement nonzero-element
structure or unit structure. All three intrinsic equations are proved by
reflexivity. In particular the construction needs no topology, continuity,
analyticity, polynomial structure, or nonzero value somewhere on its denominator.
The support can be empty.

Worker 12 authored this internal abstraction. Its provenance is the common
algebraic part of the three published formulas, rather than a new theorem
attributed to an original arithmetic source. The adapters and their comparison
statement describe the precise relationship to those specialized constructions.
