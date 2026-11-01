# Finitely many separating sections on a proper scheme

The theorem `Langlands.AlgebraicGeometry.finiteSeparatingSections` proves exactly
the published proposition
`Langlands.AlgebraicGeometry.FiniteSeparatingSectionsStatement.{u}`.
Its module is
`Langlands.AlgebraicGeometry.FiniteSeparatingSectionsProof`.

Let `K : Type u` be an algebraically closed field, let
`p : X ⟶ Spec K` be proper, and let `L` be a line bundle on `X` satisfying
`Picard.SeparatesPointsAndTangents p L`. There are a natural number `n` and
sections `s : Fin (n + 1) → SchemeModule.GlobalSections L.obj` such that:

1. every point of `X` belongs to the nonvanishing locus of some `s i`;
2. for distinct rational points `x` and `y`, a `K`-linear combination of the
   `s i` vanishes along `x` and does not vanish along `y`;
3. for every nonzero dual-number tangent vector `t` at a rational point `x`,
   a `K`-linear combination of the `s i` vanishes along `x` and does not
   vanish along `t`.

Scalars act through `Scheme.Modules.scalarsFromBase p`, and vanishing means
`Picard.VanishesAlong`, the vanishing of the pulled-back section. No claim
that a section defines a Cartier divisor is needed. The result includes all
characteristics and empty, non-reduced, and reducible schemes. The theorem
has no outer hypotheses, and `u` is arbitrary.

## Implemented proof

The helper `Langlands.AlgebraicGeometry.finiteSeparatingSections_of` in
`FiniteSeparating.Core` proves the target from the local closed-immersion
criterion. This entry supplies that premise using the published theorem
`Langlands.AlgebraicGeometry.properRationalImmersion_localClosedImmersion`
from `ProperRationalImmersionLocalClosedImmersionProof`, at universe `u`.
The core already uses the published theorem `linearSystemMorphism` from
`LinearSystemMorphismProof`. Both geometric inputs are therefore proved.

The core construction, explained in its companion, proceeds as follows.
Jacobsonness and quasi-compactness give finitely many sections without common
zeros. For each rational point, the ascending chain condition on opens gives
a finite enlargement separating it from the other rational points. The
ascending chain condition on ideals in an affine neighbourhood gives a
further finite enlargement separating its nonzero tangent vectors.

The associated linear-system morphism and its vanishing dictionaries turn
separation at this point into the hypotheses of the local closed-immersion
criterion. The resulting monomorphism over a target neighbourhood implies
separation at every rational point of its inverse image. These neighbourhoods
cover all rational points, hence the scheme by Jacobsonness. A finite
subcover and the union of its finite sets of sections give the desired family.

The helper `FiniteSeparating.Span` compares the span of a finite set `S`
with combinations of `enum S : Fin (S.card + 1) → GlobalSections L.obj`.
This enumeration starts with zero, so it is available even when `S` is
empty. Monotonicity of the span preserves separation after taking the final
finite union. The core chooses `n = S.card`.

## Provenance and authorship

This is an internal Noetherian construction. For comparison, Milne's proof
of Theorem 7.1 on pp.10–11 of *Abelian Varieties*, registered as
`milne-abelian-varieties-1986-author-2022`, uses the very-ampleness criterion
for a complete linear system. The present implementation obtains a finite
family without invoking finite-dimensionality of proper global sections.
It uses no ample-existence or downstream projectivity theorem.

Worker 898 authored the finite-span bookkeeping, conditional core proof,
and their original explanations. Worker 143 updated the core to reuse the
published linear-system proof, supplied the published local criterion here,
and prepared the unconditional theorem and submission. The companions of
the imported proofs describe their separate constructions.
