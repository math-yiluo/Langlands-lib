# The unipotent part of a smooth connected solvable group

`Langlands.GroupScheme.SolvableUnipotentPartStatement.{u}` is a
proposition target, not a proof.

Let `k : Type u` be an algebraically closed field and let `H` be a smooth
connected affine group scheme over `Spec k` that is solvable
(`IsSolvableGroupScheme H`). Then there is a homomorphism `h : Hu ⟶ H`
such that:

- `h` is a closed subgroup (`IsClosedSubgroup h`);
- `Hu` is smooth and connected and unipotent (`IsUnipotent Hu`);
- the range subgroup functor of `h` is normal in `H` on every test scheme
  (`SubgroupFunctor.IsNormal`);
- every unipotent closed subgroup `w : W ⟶ H` is contained in `Hu`:
  `SubgroupFunctor.range w ≤ SubgroupFunctor.range h`, an inclusion on
  every test scheme. `W` need not be smooth or connected.

## Source

J. S. Milne, *Algebraic Groups* (2017), Theorem 16.33, printed pp.335–336
(zero-based PDF pages 350–351). For a smooth connected solvable algebraic
group `G` over a perfect field: (a) there is a normal unipotent subgroup
`G_u` with `G/G_u` of multiplicative type; (b) `G_u` contains all unipotent
algebraic subgroups of `G`; (c) `G_u` is smooth and connected and `G/G_u`
is a torus. This statement keeps exactly the existence of `G_u` with the
properties in (a)–(c) that do not involve the quotient `G/G_u`, in the
special case of an algebraically closed (hence perfect) field. It omits
the quotient clauses, the base-change clause of (b), the uniqueness clause
of (c), and part (d).

## Encodings

- Milne's algebraic groups are group schemes of finite type over `k`.
  Here `H` is smooth (so locally of finite presentation) and affine (so
  quasi-compact), hence of finite type. `Hu` is closed in `H`, hence also
  affine and of finite type.
- Solvability is the existing Library predicate `IsSolvableGroupScheme`:
  the abstract group of points over `AlgebraicClosure k` of the base change
  is solvable. For a smooth connected group over an algebraically closed
  field this agrees with Milne's solvability (derived series of algebraic
  subgroups ending in `e`) by Milne Proposition 16.34, (c)⇔(d), printed
  p.336. Here `k → AlgebraicClosure k` is an isomorphism.
- Milne's normal subgroups and inclusions of subgroups are conditions on
  points with values in every `k`-algebra. The statement uses the existing
  Library encodings on every test scheme over `Spec k`, as in
  `Langlands.GroupScheme.ChevalleyUnipotentEnvelopeStatement`. Points of
  a closed subgroup scheme are detected on an affine open cover of the test
  scheme, so the two readings agree.
- Algebraic subgroups in Milne's sense are closed group subschemes, which
  is what `IsClosedSubgroup` encodes.

The official author errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was read; it has no
correction to Theorem 16.33 or Proposition 16.34.

## Use

This is a prerequisite for the envelope step in the proof of
`Langlands.GroupScheme.ChevalleyUnipotentEnvelopeStatement`: applied to a
Borel subgroup `B`, every conjugate of a unipotent subgroup contained in
`B` lies in `B_u`, which bounds the normal closure.

Source: `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
