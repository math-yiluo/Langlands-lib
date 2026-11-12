# Coproducts with disjoint irreducible constituents

Author: Worker 167, Task 5313 (`03088b22-a403-46ae-a6ed-6dea22f5472a`).
This is derived infrastructure for the subrepresentation argument in
Renard VI.7.2 and A.IX, specialized to actual smooth complex representations.

For any topological group, `subrepresentationCofan` takes an actual smooth
cofan and an invariant subspace `S` of its vertex. Its components are the
inverse images of `S` under the original legs, represented on their actual
submodule carriers; its vertex is the actual smooth subrepresentation `S`.

`subrepresentationCofanIsColimit` proves this cofan is a coproduct if the
original cofan is a coproduct and two distinct original components have
no common irreducible actual subquotient. It adds no finite length,
admissibility, global coproduct-existence or family-smallness premise.
The group, carrier and index universes remain independent. The disjointness
condition is an explicit hypothesis of this generic construction.

The proof first establishes two tools. `cofanIsColimitOfBijective` proves
the cofan universal property from bijectivity of its actual algebraic
summation intertwiner. The inverse of that intertwiner, followed by summation
in any target cofan, defines the descent map. Finite-support induction
proves uniqueness. The independence lemma takes invariant subspaces with no
common irreducible actual subquotients. A nonzero intersection of one subspace
with the sum of the others has an irreducible subquotient. The published
theorem `irreducibleSubquotient_iSup` puts it in another subspace, contradicting
the premise.

For the main construction, compose each original cofan leg with the quotient
by `S`. Its image is a quotient of that component, so these images still
have no common irreducible constituents. The independence lemma makes their
sum map injective. A finite-support vector whose original sum lies in `S`
maps to zero in the quotient; injectivity then forces each coordinate
image to vanish. Each coordinate therefore lies in the inverse image of
`S`. This proves surjectivity of summation from the restricted components
onto `S`. Injectivity follows from injectivity of the original summation and
the component submodule inclusions. The cofan criterion now gives the actual
coproduct. The original summation is bijective by the published
`cofanDirectSumMap_injective` and `cofanDirectSumMap_surjective`, including
when the index universe exceeds the carrier universe.

`isCoproductOfComponents_subrepresentation` expresses the result using the
published `Renard.IsCoproductOfComponents`: pairwise incompatible predicates
on irreducibles define constituent properties, and a supplied coproduct
presentation restricts to every actual subrepresentation. Subquotient
transitivity keeps the restricted components in their prescribed classes.
It does not assume or construct a partition covering all irreducibles.
The final Hom-vanishing lemma observes that a nonzero morphism has a
nonzero image and hence an irreducible actual subquotient common to its
source and target.

Source and provenance: David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, A.IX, printed p.268 / PDF
p.274, especially the subobject intersection formula in the unnumbered
Lemma; and VI.7.2, first Lemma, printed p.182 / PDF p.188. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 167 read both passages. Lean proves the intersection presentation
directly in the actual smooth category using the algebraic direct sum and
quotient images. This differs from the printed categorical empty-support
cokernel proof. It proves no unconditional cuspidal-support uniqueness or
Bernstein decomposition; applying it to Bernstein blocks requires a proof
that their irreducible support predicates are incompatible.
