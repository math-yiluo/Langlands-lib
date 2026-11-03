# The adelic parabolic Iwasawa target

`Langlands.Global.AdelicGroupPoints.ParabolicIwasawaStatement` states
Getz–Hahn, *An Introduction to Automorphic Representations* (2024), §2.7,
Theorem 2.7.1 and equation (2.24), printed p.71, for number fields. For
every number field F, connected reductive F-group G, and actual rational
parabolic inclusion p : P → G, it asks for a maximal compact subgroup K
of the existing adelic point group such that

G(A_F) = image(P(A_F) → G(A_F)) K.

The Lean statement uses the existing `AdelicGroupPoints F G` and its
existing topology. Its parabolic map is the existing continuous group
homomorphism `AdelicGroupPoints.map F P G p`, induced by the actual
group-scheme homomorphism. The image is taken on actual adelic points;
there is no substitute point group or chosen local product model.
Pointwise multiplication puts the parabolic factor on the left and the
compact factor on the right, as in (2.24).

`IsMaximalCompactSubgroup F G K` says that the underlying set of K is
compact and that every compact subgroup containing K equals K.
Maximality is among all compact subgroups of the actual ambient
topological group, without a restriction to a chosen family.
`IsParabolicIwasawaCompact F G P p K` combines that property with the
displayed exact covering equality, written in Lean as equality of the
product set with `Set.univ`.

`IsConnectedReductive G` is the existing algebraic predicate: smoothness,
affineness, connectedness and trivial geometric unipotent radical.
`IsParabolicSubgroup p` is the existing all-test algebraic notion of an
actual smooth closed subgroup containing a geometric Borel. The
statement quantifies over every such parabolic, including the improper
parabolic. It does not restrict G to a split or isotropic group, and it
does not restrict F to the rational field. The source also treats
function fields; that extension is outside this target.

These are proposition definitions. No compact subgroup is supplied as
an input to the existence target, and no compactness, maximality or
coverage theorem is asserted by this module. Proving the target must
construct the compact subgroup in the actual adelic topology and prove
all three properties. It remains separate from minimal-parabolic and
derived-torus existence, compatible Haar measures, Siegel-set coverage,
finite volume and height independence. In particular, the target does
not identify arbitrary compact data in `AdelicSiegelFactors` with an
Iwasawa compact subgroup.

The original p.71 theorem was checked in the registered book, including
the order in (2.24). The five-page October 2026 author errata was checked;
it contains no correction to Theorem 2.7.1 or equation (2.24). The book
refers to Appendix B for a proof sketch. This module records the read
theorem statement, without claiming a reading or formal implementation
of that proof.

Source records: `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`,
§2.7, Theorem 2.7.1, equation (2.24), printed p.71;
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
October 2026, all five pages.
