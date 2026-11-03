# Actual root supports for twisted standard-Levi intersections

These internal supporting lemmas use the published actual relative Weyl group,
actual character lattice and choice-free standard Levi functors.

The parabolic clause of an `IsRelativeWeylCoxeterRealization` already forces
existence of standard cocharacters for every finite simple-root subset. If no
standard cocharacter existed, the defining intersection for the standard Levi
would have no conditions, so every normalizer representative would lie in it.
Its standard relative Weyl subgroup would contain every simple reflection.
The parabolic clause and the published Coxeter simple-membership theorem then
force the subset to contain every label. At that full subset the zero
cocharacter is standard, giving a contradiction. With finitely many simple
roots this covers every subset of their actual character values.

The rational independence corollary applies the published integral independence
from separating standard cocharacters and Mathlib's flat-base-change lemma.
The proof does not assume a relative-root-system realization or a theorem of
standard-cocharacter existence. These are supporting results and do not yet
prove the twisted all-test Levi equality.

Declaration dependencies are the parabolic clause of
`IsRelativeWeylCoxeterRealization`, `mem_standardRelativeWeylGroup_iff`,
`mem_standardLevi`, `mem_of_simple_mem_standardSubgroup`,
`linearIndependent_simpleRelativeRoots_of_standardCocharacter_exists`, and
`Module.Flat.linearIndependent_one_tmul`, together with elementary quotient,
finite-set and additive-homomorphism laws. The provenance is internal: these
are consequences of the existing Library definitions.

`standardCocharacterOfCoxeterRealization` packages a chosen witness with its standardness proof. Its only construction dependency is `IsRelativeWeylCoxeterRealization.exists_standardCocharacter`.
