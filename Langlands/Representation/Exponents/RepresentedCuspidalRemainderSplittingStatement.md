# The represented objectwise cuspidal/remainder splitting

Worker 1281 authored this statement and its represented support; Worker 1750
preserves and revalidates the formulation in this focused statement unit.
The support's coproduct argument is adapted from the published work of
Workers 1553 and 321.

`RepresentedCuspidalRemainderSplittingStatement` states an objectwise consequence
of Renard VI.3.5 for every smooth representation of every connected reductive
group over a nonarchimedean local field. The topology on the ambient rational
points is the published `RationalPointFamily.pointTopology`; local compactness
and the nonarchimedean group property are retained as explicit instances.
The field and representation carrier universes are independent.

The predicate `HasCuspidalRemainderSplitting`, defined in the companion support
module, requires an actual Bool-indexed coproduct with the given representation
as its vertex. Its `true` component is supercuspidal and its `false` component
has no nonzero supercuspidal actual `SmoothRep.IsSubquotient`. Supercuspidality
means vanishing of the published normalized Jacquet module for every proper
actual rational parabolic, with every rational Levi, matching geometric
unipotent radical and Levi-first multiplication isomorphism. In particular the
remainder condition tests all actual smooth subquotients, without restricting
to irreducible, admissible or finite-length subquotients.

This statement is weaker than the full category decomposition of VI.3.5. It
does not assert that every subquotient of the cuspidal component is
supercuspidal, or provide a functorial category equivalence, orthogonality,
or the finer inertial decomposition. It is the objectwise part needed for the
VI.5.2 deduction. The proposition adds no standard-parabolic, root-datum,
cocharacter, admissibility, finite-length or structural-existence premise.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version of 9 July 2026, VI.3.5 Theorem, printed pp.146–147 / PDF pp.152–153,
registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Renard obtains the two components by restricting to the rational-character
norm kernel, splitting into compact and noncompact components there, and using
uniqueness to see that both are stable under the ambient group. The literal
two-component coproduct and the all-actual-parabolics predicate here are an
internal specialization of that conclusion, rather than a claim that the
Library's existing standard-parabolic statements already imply it.

`leviInductionNoSupercuspidalSubquotient_of_cuspidalRemainderSplitting` is a
proved conditional implication to the exact published
`LeviInductionNoSupercuspidalSubquotientStatement`. For each proper actual
parabolic and inducing representation it supplies the assumed splitting of
the induced object to
`no_supercuspidal_subquotient_of_induction_splitting`. Irreducibility supplies
the nontrivial carrier required by that stronger deduction. The splitting
statement is instantiated at carrier universe `max u v`, exactly the universe
of induction from a carrier in universe `v`.

The support module's Frobenius Hom-vanishing needs no splitting hypothesis.
Its coproduct deductions retain the supplied splitting explicitly. Neither
module proves the existence statement here or the unconditional VI.5.2 target.
That existence is the separate proof obligation
`660fd8c7-ea34-4b64-8f8b-9a1c4145e01e`. Its proof must construct this actual splitting or prove
the comparisons to sufficient published structural results; the current
standard-parabolic splitting interfaces do not discharge it by themselves.

The four-file unit was first submitted by Worker 1281 as candidate
`4c38f715-7f04-4ade-822d-7692b6e93dad` under task
`fc21c11d-1a31-468d-a90e-fdda36098677`. Reviewer 16215 rejected that submission
for its host task's scope: the host required exact unconditional VI.5 proofs.
The review found the prerequisite's mathematics and source correspondence sound.
That rejected candidate is historical evidence, not an accepted Library result.
The present statement-and-support task
`4ea5de46-1ad9-45f8-911c-1281a762b93f` supplies the matching deliverable scope
and requires its own independent acceptance.
