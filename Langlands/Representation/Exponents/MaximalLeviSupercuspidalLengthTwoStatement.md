# Length two for represented maximal-Levi supercuspidal induction

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, VI.5.4 (printed pp.173–174 / PDF pp.179–180),
V.4.8 (printed p.122 / PDF p.128) and the application VII.1.3 (printed pp.224–226 / PDF pp.230–232).
Literature ID: `renard-2026-representations-groupes-reductifs-padiques`.

`MaximalLeviSupercuspidalInductionLengthBoundStatement.{u,v}` states the
maximal-Levi specialization of VI.5.4's bound. It quantifies over a nonarchimedean
local field in universe `u`, an actual connected reductive group, and a proper
maximal represented rational parabolic, with the specified rational Levi,
geometric unipotent radical and multiplication isomorphism. Maximality means
that every factorization through a rational parabolic has an isomorphism as
one of its two factors. The ambient group has the pinned canonical point
topology and is locally compact and nonarchimedean. The Levi has its own
`leviPointTopology`, with the published local compactness and nonarchimedean
instances. All of these binders agree with the interface of the unitarizable
constituent statement.

The inducing object `ρ : SmoothRep.{0,u,v} ℂ M(k)` is irreducible and
supercuspidal in the sense that every normalized Jacquet module for every
proper represented parabolic of `M` is zero. There is no finite-length input
and no central-character condition. The conclusion is
`repLength (i_P ρ).representation ≤ 2`, where the actual induced carrier is in
universe `max u v`. This is a bound on actual composition length, including
multiplicities. Renard first bounds it by `l(M)`; V.4.8 identifies `l(M)` with
two for a maximal Levi. The statement includes arbitrary represented
parabolics, as does the theorem VI.5.4 before its proof reduces to standard ones
by conjugation.

`MaximalLeviSupercuspidalInductionLengthTwoStatement.{u,v}` adds the premise
that the induction is reducible and concludes that there are two actual smooth
irreducible representations `π₁, π₂`, in the same carrier universe `max u v`,
and actual equivariant linear maps
`π₁ → i_P ρ → π₂`. The first is injective, the second surjective, and the image
of the first equals the kernel of the second. This is the short exact sequence
(VII.1.3.2), so the statement also excludes zero endpoints through irreducibility.
It imposes no unitarity or central-character assumptions.

These two declarations are proposition statements. The represented length
bound is not proved here. The companion reduction module proves nonzeroness
of the actual represented induction and derives the endpoint statement from
the length-bound statement using the published algebraic two-factor extraction.

The older 2010 errata, PDF p.13, corrects the earlier length wording to
“less than or equal to” and fixes the adjunction paragraph's `P′, M′` indices.
The 2026 passage uses the corrected non-strict bound and indices. No
source-specific project errata note was present in the checked notes paths.

Worker 1658 authored the statements and reduction. Worker 1714 contributed
to the endpoint-interface design for their common unitarizable-constituent task.
