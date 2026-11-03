# Geometric nilpotence for smooth group schemes

Author: Worker 1487.

`IsNilpotentGroupScheme G` means that the abstract group
`G_{k̄}(k̄)` is nilpotent, where `k̄ = AlgebraicClosure k` and the base change
and point group are the actual published group-scheme constructions.
The definition permits any field `k : Type u`, with arbitrary universe,
characteristic and perfectness. It follows the geometric-point convention
of the published `IsSolvableGroupScheme`.

This geometric predicate is intended for smooth group schemes. It makes
no assertion about the nonreduced structure of a nonsmooth group scheme.
In particular, the definition is not a new all-test definition of
nilpotence for arbitrary group schemes.

The lemma `IsNilpotentGroupScheme.isSolvableGroupScheme` is proved by the
Mathlib instance that a nilpotent abstract group is solvable, applied to
this same group of geometric points. Smoothness and connectedness are not
needed for this lemma about the two geometric predicates.

## Source correspondence and intended use

Milne, *Algebraic Groups* (2017), Proposition 16.49, printed p.342
(one-based PDF p.358), says that a smooth connected algebraic group over
an algebraically closed field is nilpotent exactly when its abstract
group of rational points is nilpotent. Thus for a smooth connected affine
group over `k`, the present definition tests the classical nilpotence of
its algebraic-closure base change. The classical central-series condition
descends to `k`: equivalently, a fixed iterated commutator morphism is the
constant identity morphism, and equality of morphisms descends under a
field extension.

The definition is introduced for the nilpotent cases of Milne's
Proposition 17.81 and Theorem 17.91. Theorem 16.47, printed p.341
(PDF p.357), supplies a central torus with unipotent quotient in the
smooth connected case; that structure theorem remains a separate
statement and proof obligation. This module neither constructs the
torus nor proves the central-series comparison.

The original source is registered as `milne-2017-algebraic-groups`.
The full official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was read; its Chapter 16
entries do not alter Theorem 16.47 or Proposition 16.49.
