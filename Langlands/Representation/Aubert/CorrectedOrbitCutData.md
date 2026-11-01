# Radical intersections and orbit representatives across source cuts

This internal construction compares the actual stabilizer intersections used
in the parabolic orbit integral. If `B.cuts ⊆ D.cuts` and `w` increases on
every block of `B`, then the subgroups
`parabolicOrbitRadicalIntersection R B C w` and
`parabolicOrbitRadicalIntersection R D C w` of the actual target radical
are equal. The result holds over every commutative ring and in every rank;
it does not require an association hypothesis or inverse monotonicity.

The proof uses the ambient matrix criterion for parabolic membership.
Adding cuts shrinks the source parabolic, giving one inclusion. For the
other inclusion, consider an entry below the finer block diagonal. If its
coordinates already lie in distinct coarse blocks, the entry vanishes by
the original parabolic membership. If they lie in one coarse block,
source monotonicity orders their images under `w`. The target radical
has zero at that image entry. The actual permutation conjugation formula
transports this zero back to the required entry.

`parabolicOrbitRadicalIntersectionEquiv` packages this equality as the
canonical group equivalence between the two actual radical stabilizers.
The evaluation lemma records that it preserves the underlying target
radical element. Thus the identification transports subgroup membership
without changing integration coordinates.

The second theorem, `correctedInductionOrbit_cutMap_projection_eval`,
compares the actual orbit restriction maps on corrected normalized
induction support quotients. Start with a smooth ambient representation
`A`, a length-upper set `θ` with length-upper singleton removal, and an
active `w` for source `B` and target `C`. Apply the actual `Transition.cutMap`
to an upper-support representative. The proved support preservation places
the result in the finer source's upper support, and monotonicity of the
corrected Weyl support makes the same singleton active there. Restricting
its quotient class to the orbit gives, at every target parabolic element,
the actual Jacquet quotient projection of the original restricted value.
Both restrictions evaluate the same function at the actual inverse
permutation representative. The cut map evaluates by that quotient
projection, so the square follows without a scalar factor.

These are internal consequences of the existing block, permutation,
corrected support and transition definitions. They supply a common domain
for later orbital integrals and identify their pre-integration functions.
They do not yet compare the integrals, their normalizations, the exterior
signs, or the homology of the Aubert complex.
