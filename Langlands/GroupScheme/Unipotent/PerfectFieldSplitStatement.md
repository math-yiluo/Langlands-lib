# Smooth connected unipotent groups over perfect fields are split

Worker 1448.

`Langlands.GroupScheme.PerfectFieldUnipotentSplitStatement.{u}` is a
proposition definition. For every perfect field `k : Type u` and actual
group scheme `U` over `Spec k`, it assumes smoothness, an affine structure
morphism, connected underlying space, and the unchanged fixed-vector
predicate `IsUnipotent U`. Its conclusion is the existing
`RelativeRoot.IsSplitUnipotent U`.

The universe is arbitrary. The field may be finite or infinite, and every
characteristic is included. The trivial group is included, with the empty
series as the appropriate witness. Smoothness implies local finite
presentation and therefore local finite type; affineness makes the
structure morphism quasi-compact. Consequently the hypotheses place `U`
in the affine finite-type setting of the source without a separate
finite-type premise.

The conclusion supplies a natural number `n` and an actual
`RelativeRoot.HasSplitSeries n U`. Every successor step has an actual
smooth connected closed normal subgroup and an actual group-scheme
quotient map. Its quotient is a one-dimensional vector group, encoded by
natural multiplicative equivalences of its point groups on every relative
scheme with the additive group of one global function. The map is flat,
scheme-surjective and locally of finite presentation. Its actual kernel
has exactly the prescribed subgroup image on every relative scheme test.
At length zero the identity homomorphism has bottom image on every test,
so the terminal represented group functor is trivial. This conclusion
uses the imported definitions unchanged; it neither assumes a series nor
replaces a represented quotient with a quotient of rational-point groups.

## Original source and scope

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (2017), Corollary 16.24, printed p.331 / one-based PDF p.347,
asserts a central normal series with Ga quotients for every smooth
connected unipotent algebraic group over a perfect field. The source
proves it from Corollary 16.23, which uses Corollary 16.22 and Theorem
16.21. These passages are at printed pp.330–331 / PDF pp.346–347.

The Lean proposition records the non-equivariant splitness consequence.
It does not assert centrality of the series or stability under an
additional torus action. Ga is the one-dimensional vector group under the
natural all-test convention used by `IsVectorGroupOfDimension`. The
source's algebraic-group quotients translate to actual represented fppf
quotient maps with their scheme kernels, as required by the existing
`IsFppfQuotient` predicate. Establishing those maps and comparisons is part
of a proof of this target, not data supplied as a hypothesis.

The registered source ID is `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The complete official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
was read and gives no correction to Corollaries 16.22–16.24 or Theorem
16.21.

This module supplies no proof. It isolates the unipotent Ga-series input
for the algebraically closed solvable split-series proof. It makes no
Borel-conjugacy assertion and assumes no Borel subgroup, embedding,
chosen quotient or normal series.
