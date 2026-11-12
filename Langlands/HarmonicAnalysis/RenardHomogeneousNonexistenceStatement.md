# Renard II.3.9: untwisted invariant distributions need not exist

This focused statement records the introductory warning of David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, II.3.9, printed p.48 / PDF p.54, first paragraph. Source ID:
`renard-2026-representations-groupes-reductifs-padiques`; SHA256:
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

`Langlands.HarmonicAnalysis.HomogeneousFunctions.Renard.NonexistenceStatement`
asserts that there exist a small locally profinite topological group `G` and
an actual closed subgroup `H` such that the full algebraic dual of the ordinary
Schwartz–Bruhat space on `H\G` has no strictly positive functional invariant
under all right translations. The group structure, topology and topological
group instance are existentially supplied and installed on that same type.
Locally profinite means the existing
`Langlands.Topology.IsLocallyProfinite`, including Hausdorffness.

The quotient is the published `Langlands.Induction.LeftQuotient H`, with its
quotient topology. The homeomorphism
`Langlands.QuotientIntegration.rightTranslate H g` sends `H*x` to `H*(x*g)`;
`Distribution.pushforward` is the existing transport on the full algebraic
dual. Invariance for every `g` is independent of replacing each parameter by
its inverse. Positivity is the existing `Distribution.IsPositive`: every
nonzero real-valued nonnegative test has a real strictly positive value.
Thus the zero functional is excluded by the same convention as the Haar and
homogeneous-space theorems in II.3.6 and II.3.9.

The source first mentions failure of a left-invariant measure on `G/H`, then
switches to `H\G` and right translations. Inversion identifies those two
homogeneous spaces and exchanges the actions, so the statement uses the latter
orientation throughout. It expresses the warning in the source's distribution
language on the untwisted quotient, without asserting that the twisted space
of the subsequent Theorem lacks a positive invariant functional.

This is a closed existential `Prop` definition, with no constructed witness or
proof. It leaves the existing twisted-space theorem target and its proof task
unchanged. The published compatible quotient-measure existence theorem under
regular two-sided Haar hypotheses is a restricted positive case; it does not
assert existence for arbitrary closed subgroups and does not discharge this
nonexistence statement.
