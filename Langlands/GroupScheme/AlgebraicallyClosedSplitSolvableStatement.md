# Solvable groups are split over an algebraically closed field

Worker 1364.

`Langlands.GroupScheme.AlgebraicallyClosedSplitSolvableStatement.{u}`
records a proposition definition. For every algebraically closed field
`k : Type u` and every actual group scheme `H` over `Spec k`, it assumes
smoothness, an affine structure morphism, connected underlying space, and
the unchanged `IsSolvableGroupScheme H`. It concludes the unchanged
`IsSplitSolvableGroupScheme H`. Every characteristic and the trivial group
are included.

The conclusion includes a finite `SplitSolvable.HasSeries n H`. At each
successor step this gives an actual smooth connected closed normal subgroup
and an actual represented fppf quotient over `k`. Each quotient is a
one-dimensional vector group or is isomorphic as a group scheme to Gm.
The quotient map is flat, surjective and locally of finite presentation,
and its actual scheme kernel equals the prescribed subgroup functor on
every relative scheme test. The zero step says that the represented group
functor is trivial on every test. The conclusion also retains smoothness,
affineness, connectedness and the original geometric-point solvability
predicate.

Thus the statement supplies a scheme-theoretic series, not merely an
abstract series of rational-point groups. It assumes no chosen embedding
in a general linear group, unipotent subgroup, torus quotient, normal
series or Borel subgroup.

## Source and comparison

Milne, *Algebraic Groups* (2017), Proposition 16.34, printed p.336,
one-based PDF p.352, states that over an algebraically closed field the
following conditions on an algebraic group are equivalent: being split
solvable; being smooth and connected with solvable abstract rational-point
group; being smooth, connected and solvable; and being smooth, connected
and trigonalizable. This target specializes the implication from
smoothness, connectedness and rational-point solvability to split
solvability, using the Library's existing geometric-point solvability
predicate. The latter implies rational-point solvability by extending
sections to the actual algebraic-closure base change and using injectivity
of that extension. This comparison is a proof obligation, not an extra
assumption in the statement.

Milne's algebraic groups are affine of finite type. The Lean hypotheses
retain finite type because smoothness gives local finite presentation and
the affine structure morphism is quasi-compact. A proof must construct
the actual series and establish all its represented quotient properties;
the proposition does not assume these properties. Milne's route through
the Lie–Kolchin theorem (16.30, printed pp.334–335, PDF pp.350–351) and
Corollary 16.22 (printed p.331, PDF p.347) is upstream of Borel conjugacy.
The implication is also stated explicitly in Proposition 16.34.

The vector-group convention in the imported predicate requires natural
multiplicative equivalences of the point functors with the additive group
of one global function, on every relative test scheme. Identifying an
actual Ga quotient with that convention, and identifying the source's
quotients with the imported `RelativeRoot.IsFppfQuotient`, remain part of
the proof. No surjectivity on every original test's point group is
asserted.

Registered original: `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The complete registered official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
was read and contains no correction to Proposition 16.34, Theorem 16.30
or Corollary 16.22.

This module supplies no proof of the comparison or of a fixed-point
theorem. It isolates a substantial structural prerequisite for the
split-solvable route to `SolvableProperFixedPointStatement`. That route
also needs the pseudo-complete fixed-point theorem, properness implying
pseudo-completeness and existence of an initial rational point. The
closed-orbit route to the same fixed-point target is a separate route.
