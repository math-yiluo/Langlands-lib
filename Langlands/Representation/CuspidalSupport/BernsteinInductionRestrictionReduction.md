# Formal support steps for Bernstein induction and restriction

Worker 1437 names the literal fibre predicate in the published
`BernsteinInductionRestrictionStatement` as `bernsteinLeviFibreProperty`.
Every irreducible subquotient is required to occur in normalized induction
inside `M_J` from a genuine cuspidal datum with roots inside `J` and ambient
inertia class `[a]`. All carriers remain in `max uF uV`, with the two
universes independent.

`bernsteinLeviFibreProperty_of_jacquetExclusion` proves the restriction
assertion from the explicit hypothesis `BernsteinJacquetExclusion` on the
ambient representation. For any irreducible subquotient of its normalized
Jacquet module along `J`, the same-datum inner presentation theorem supplies
both an induction embedding and a quotient of a smaller inner Jacquet
module. Exact inner Jacquet restriction and Jacquet restriction in stages
put that cuspidal datum in the corresponding ambient Jacquet module. Ambient
exclusion forces its inertia class to equal `[a]`. Its induction embedding
then gives the required fibre witness. No inner-Levi support existence or
support comparison hypothesis remains in this implication.

`bernsteinLeviFibreProperty_of_blockCharacterization` applies the forward
direction of characterization (iii), retaining the published global
characterization proposition as an explicit premise.
`bernsteinLeviFibreProperty_of_embedding_and_exclusion` instead uses the
published characterization reduction, leaving only the fixed-Levi block
embedding and geometric induced-inertia exclusion steps as explicit
premises. Both deductions apply to arbitrary smooth ambient block members.

`bernsteinInduction_mem_block_of_leviPresentation` proves induction block
membership whenever the input has one inner cuspidal induction-subquotient
presentation of the specified ambient inertia class. Exact induction and
induction in stages transport the presentation to ambient induction of the
same datum. The published theorem that defining induction lies in its saturated block,
closure under subquotients, and invariance of inertial support under related
datum representatives then give the specified block membership. A private
helper proves closure with abstract representation arguments; the stages
implication is first specialized to its input representations before its
subquotient witness is supplied.

`bernsteinInduction_mem_block_of_irreducible_fibre` applies this result to
an irreducible fibred input, using that input as its own subquotient.
This does not prove induction preservation for an arbitrary smooth fibred
input. Exactness and induction in stages alone do not provide the generation
or embedding statement needed for that extension. Nor does the restriction
implication prove that every ambient block member satisfies Jacquet
exclusion. These two obligations remain explicit; the full published
proposition is not proved here.

These are internal deductions from the Library's actual normalized functors,
subquotient calculus, genuine Bernstein data and support presentations.
The source context is Renard, *Représentations des groupes réductifs
p-adiques*, French version of 9 July 2026, VI.7.3 (printed p.185 /
PDF p.191), registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The published target and all of its imports are unchanged.
