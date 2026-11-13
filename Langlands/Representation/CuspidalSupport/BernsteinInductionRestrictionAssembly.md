# Bernstein induction and restriction from decomposition and characterization

`BernsteinInductionRestrictionAssemblyStatement` is the conditional implication
from `BernsteinDecompositionStatement` at carrier universe `max uF uV` and
`BernsteinBlockCharacterizationStatement` at the independent universes `uF`,
`uV` to the exact published `BernsteinInductionRestrictionStatement`.
`bernsteinInductionRestriction_of_decomposition_and_characterization` proves
this implication. The original target pair and all its imports are unchanged.
Neither global premise is proved by this module.

The assembly first removes a separate support-uniqueness premise. An actual
inertial-support presentation of an irreducible representation places that
representation in its saturated block: each irreducible subquotient also
occurs in induction of the presenting cuspidal datum, by transitivity of
actual subquotients. Two support classes would therefore place the same
nonzero irreducible in both blocks. The off-diagonal Hom vanishing in
category decomposition would make its identity zero, a contradiction.
The proof uses actual block membership and no assumed support partition.

The literal fibre predicate passes to subquotients, again by transitivity.
The previously proved induction theorem for irreducible fibred inputs and
restriction of ambient block members into the fibre then meet the premises
of `bernsteinInduction_mem_block_of_restriction`. Its decomposition and
normalized first-adjointness argument applies to arbitrary smooth inputs;
there is no finite-length or admissibility hypothesis. Orthogonality supplies
the inertial-support uniqueness required by that theorem.

Finally, the block characterization premise supplies ambient Jacquet
exclusion and hence the whole restriction implication via
`bernsteinLeviFibreProperty_of_blockCharacterization`. The preceding arbitrary
induction result supplies the other conjunct. The named fibre predicate is
definitionally the fibre in the published proposition, and the normalized
Jacquet functors agree by definition.

This is a derived internal reduction in the context of Renard,
*Représentations des groupes réductifs p-adiques*, French version of
9 July 2026, VI.7.2 and VI.7.3 Proposition (printed p.185 / PDF p.191),
registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Its proof composes the Library's actual normalized functors, support
presentations, block orthogonality and the published arbitrary-input
reduction by Worker 4822. The two explicit global hypotheses remain
necessary inputs to this proof; it is not an unconditional proof receipt
for the host task.
