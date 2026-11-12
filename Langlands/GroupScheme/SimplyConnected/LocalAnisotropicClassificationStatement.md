# Local anisotropic simply connected classification

Author: Worker 165.

## Statement

`Langlands.GroupScheme.LocalAnisotropicSimplyConnectedClassificationStatement.{u}`
says that an affine, anisotropic, simply connected, absolutely almost-simple
group scheme `G` over a nonarchimedean local field `K : Type u` is isomorphic
over `K` to `CentralSimpleUnits.normOne K D` for some finite-dimensional
central division `K`-algebra `D : Type u`.

The hypotheses on the field are `[Field K] [ValuativeRel K]
[TopologicalSpace K] [IsNonarchimedeanLocalField K]`. The group has
`[IsAffineHom G.X.hom]`, `IsSimplyConnected G`,
`IsAbsolutelyAlmostSimple G` and `IsAnisotropic G`. The last predicate means
`splitRank G = 0`, or equivalently that every closed split subtorus is trivial.
The conclusion supplies `[DivisionRing D]`, `[Algebra K D]`,
`[FiniteDimensional K D]`, `[Algebra.IsCentral K D]` and
`Nonempty (G ≅ CentralSimpleUnits.normOne K D)`. The division-ring instance
supplies `IsSimpleRing D`, needed by that model.

`CentralSimpleUnits.normOne K D` is the actual kernel of the reduced-norm
character on the group scheme of units of `D`. Its points on a coefficient
algebra are the reduced-norm-one units of the corresponding scalar extension
of `D`. The isomorphism in the conclusion is an isomorphism of group schemes
over `Spec (CommRingCat.of K)`, so the statement requires this algebraic-group
identification, not just an abstract isomorphism of groups of `K`-points.

There is no restriction on the characteristic of `K` or its residue field.
In particular, both characteristic 2 and residue characteristic 2 are
included. The universe `u` is arbitrary, and both `K` and `D` lie in it.
The statement asserts only this forward classification. It supplies no proof.

## Source and specialization

F. Bruhat and J. Tits, *Groupes algébriques simples sur un corps local*,
in T. A. Springer (ed.), *Proceedings of a Conference on Local Fields*
(Driebergen 1966), Springer, 1967, pp. 23–36, registered as
`springer-1967-conference-local-fields`:

- The introduction, printed p. 23 / PDF p. 29, fixes the context of simple
  simply connected algebraic groups.
- Section 4, printed p. 29 / PDF p. 35, treats a complete discretely valued
  field `K` with perfect residue field `k`, in arbitrary characteristic.
- Section 8, Proposition 6, printed p. 35 / PDF p. 41, shows that if
  `dim k ≤ 1` and `G` is `K`-anisotropic, then `G` has type `A_n`. If also
  the Galois group of the maximal unramified extension of `K` over `K` is
  commutative, `G` is an inner form of `A_n`, and its rational group is
  identified with the reduced-norm-one elements of a central division
  algebra over `K`.

For a nonarchimedean local field, the residue field is finite, hence perfect
and of cohomological dimension at most one; its absolute Galois group is
procyclic and thus commutative. The hypotheses of Proposition 6 therefore
hold. The source's inner-type classification of the simply connected group
is expressed here by its algebraic model `SL_1(D)`, rather than by the
source's notation for rational points. Establishing the group-scheme
isomorphism is part of the proof obligation: an abstract rational-point
isomorphism alone would not prove this statement.

For comparison, J. Tits, *Classification of algebraic semisimple groups*,
Proc. Sympos. Pure Math. 9 (1966), registered as
`tits-1966-classification-algebraic-semisimple`, §3.3.3, printed p. 47 /
PDF p. 52, gives the anisotropic inner-type-`A_n` conclusion over the
`p`-adic numbers. Table II, type `¹A_n`, printed p. 55 / PDF p. 60,
describes its representative as `SL_{r+1}(D)`, with `D` central division
and `d(r+1) = n+1`; `r = 0` gives `SL_1(D)`. The table describes strict
isogeny classes, so the simply connected hypothesis matters when identifying
the actual group with this representative. The arbitrary-characteristic
scope here uses Bruhat–Tits, not a claim that Tits's §3.3.3 already has that
scope.

The Library's `IsAbsolutelyAlmostSimple` allows a finite center and
corresponds to the source's absolute simplicity convention for these
semisimple groups. `IsSimplyConnected` is algebraic simple connectedness:
every central isogeny from a semisimple group to `G` is an isomorphism.
The explicit affine hypothesis is retained to match the rank-one
classification task.

## Role in the rank-one classification

This is a focused prerequisite for
`Langlands.GroupScheme.LocalRankOneClassificationStatement`, following the
anisotropic-kernel route described in Task 5442. It neither asserts nor
proves the rank-one list. Applying it to absolutely almost-simple factors
of anisotropic kernels, establishing the admissible Tits indices and
identifying the surviving classical models remain separate obligations.
It does not use a local Kneser–Tits statement.
