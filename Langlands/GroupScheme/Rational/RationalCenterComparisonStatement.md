# Comparing the scheme center with the abstract rational-point center

Author: Worker 101.

This module gives the separate scheme-center/abstract-center comparison
target needed by the consumers of WST-CEN-01. Both declarations are
`Prop`-valued definitions. They supply no equality proof and do not add a
comparison field to the structure of a reductive group.

## Exact comparison and consumer adapter

For any group scheme `M` over a commutative ring `F`,
`RationalCenterComparison M` is the equality of subgroups of the very same
actual group `rationalPoints M`:

```text
schemeCenterPoints M = Subgroup.center (rationalPoints M).
```

The left subgroup evaluates the published all-test scheme-center functor at
`Spec F`. It requires commutation after every map of test schemes, including
nonreduced tests. The right subgroup requires commutation only with elements
of `M(F)`. `schemeCenterPoints_le_center` and `schemeCenterPointsToCenter`
already supply the forward inclusion and its inclusion homomorphism. Their
surjectivity, equivalently the reverse inclusion in this equality, is the
new target.

`RationalCenterComparisonStatement.{u}` universally quantifies `F : Type u`
with `Field F`, `ValuativeRel F`, `TopologicalSpace F` and
`IsNonarchimedeanLocalField F`, and every actual `M` with
`IsConnectedReductive M`. There is no restriction on the characteristic or
on the smoothness or connectedness of the center. The per-group predicate
can be defined over any commutative ring; the closed target asserts it only
in this local-field reductive scope.

This is the precise necessary comparison for the abstract-group consumers.
If the equality is proved, transport along it identifies the two subgroups
inside `M(F)` by their unchanged ambient values. After explicitly installing
`rationalPointTopology F M.X`, their subgroup topologies are the same
induced topology. For any actual central map `i : H ⟶ M`, the already
proved `centralRationalPointImage_eq_subgroupOf` identifies the denominator
with

```text
(rationalPoints.map i).range.subgroupOf (schemeCenterPoints M).
```

Transport therefore gives precisely the consumer quotient

```text
Subgroup.center (rationalPoints M) /
  (rationalPoints.map i).range.subgroupOf
    (Subgroup.center (rationalPoints M)),
```

with its inherited and quotient topologies. The equality would thus provide
an algebraic and topological adapter for `CentralPointQuotient`; no
independent choice of a center is needed. This file states the equality,
not an already constructed unconditional homeomorphism.

## Original sources and route

Milne, *Algebraic Groups* (2017), source `milne-2017-algebraic-groups`,
Proposition 1.92, printed p.33 / PDF p.49, defines the scheme centralizer by
commutation after every extension of test algebras. Printed p.34 / PDF p.50
defines the center as the centralizer of the group itself. The Library uses
all schemes over the base as tests; the algebraic construction and its
extension from affine tests remain part of the scheme-center interface.

Proposition 1.93 on printed p.34 / PDF p.50 states that for a smooth
algebraic subgroup `H`, when `H(k')` is dense in `H`, the `k`-points of
its scheme centralizer consist exactly of the `k`-points centralizing
`H(k')`. Taking `H = M` and `k' = F` gives the required equality once
rational-point density is established. Smoothness here is smoothness of
`M`, already in `IsConnectedReductive M`; the center may be nonsmooth.
Remark 1.97, printed p.35 / PDF p.51, explicitly exhibits this distinction
with the nonreduced center `μ_p` of `SL_p`.

The needed rational-point density is Milne Theorem 17.93(b), printed p.382 /
PDF p.398: a reductive group is unirational over its field of definition,
and its rational points are dense when the field is infinite. Part (b)
does not require a perfect base field. Its proof uses Cartan subgroups
being tori and the unirationality of tori, Proposition 12.64, printed
p.251 / PDF p.267. This is the applicable clause for equal-characteristic
local fields, which need not be perfect. Theorem 17.33 in Section 17.c,
also called a density theorem, concerns conjugates of a torus centralizer
over an algebraically closed field; it is not the rational-point density
assertion being used here.

The complete official errata snapshot of 2 November 2026, source
`milne-2017-algebraic-groups-errata-2026-11-02`, was read; no listed
correction changes Propositions 1.92--1.93 or Theorem 17.93. Renard's
9 July 2026 edition, source
`renard-2026-representations-groupes-reductifs-padiques`, V.2.1, printed
p.104 / PDF p.110, writes `Z(G)` for points of the algebraic center and
introduces the split component and canonical point topology. It motivates
this consumer notation but is not used to silently equate the two centers.

The proposed proof must implement density and the closed equalizer of
conjugation by a rational point with the identity, or an actual instance of
Milne 1.93, and connect it to the all-test center. None of these
mathematical results is proved by defining this proposition. Compactness is
the independent `CenterSplitComponentCompactnessStatement`; it is neither
assumed nor asserted by the comparison target.
