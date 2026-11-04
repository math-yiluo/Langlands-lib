# Rational conjugacy through a split unipotent quotient

This internal construction lifts an actual specified rational conjugator from
a represented quotient and proves the exact conjugation and projection equations.
It specializes the existing three-input split unipotent cocycle construction
using the published proof `splitUnipotentAffineTorsorStatement`. Two global
propositions remain explicit: `SplitUnipotentStableVectorSubgroupStatement`
and `TorusVectorActionLinearizationStatement`. It does not prove either
proposition or the full solvable maximal-torus conjugacy statement.

All fields at universe `u`, including finite and imperfect fields, are retained.
The torus may be nonsplit. Neither homomorphism from a torus needs to be
injective, closed, or maximal. The quotient is supplied; no quotient existence
is asserted.

## Actual rational lifts

Let `G` be an affine group scheme over a field, `n : N → G` a smooth closed
split unipotent subgroup, and `q : G → Q` satisfy the existing
`IsFppfQuotient (SubgroupFunctor.range n) q` predicate. No affineness or
smoothness of `Q`, connectedness of `N`, or smoothness of `G` is assumed
for the lifting step.

`HomogeneousQuotient.fppf_affine_lifts_of_split_unipotent` proves that every
point of `Q` on every affine scheme over the field lifts to `G`. Closedness
supplies monicity and affineness of `N`. The quotient predicate supplies
flatness, surjectivity, and exact all-test right-coset fibers of `q`.
The published `fieldSeparated` theorem makes `Q` separated over the field.
Quasi-compactness of `q` then follows from affineness of `G` over the field:
`q` composed with the structure morphism of `Q` is the structure morphism
of `G`, and the second factor is quasi-separated. The existing affine-test torsor adapter then applies with the
published affine torsor proof. This uses an affine test and does not require
the whole quotient scheme to be affine.

`splitUnipotentRationalLift` chooses this lift on the test `Spec k`;
`splitUnipotentRationalLift_comp` proves that its composite with `q` equals
the original specified point. These constructions require neither of the
two remaining global propositions.

## Correcting a supplied lift

The lower-level construction takes a monic `n : N → G` whose represented
range is exactly the represented kernel of `q`. Here `N` is smooth,
connected, affine, unipotent and split unipotent, using the existing
predicates. There are maps `i : H → G`, `i' : H' → G`, with `H` a torus,
and an isomorphism `f : H ≅ H'`. An actual rational point `x` of `Q`
satisfies

`(i ≫ q) ≫ inner(x) = f.hom ≫ (i' ≫ q)`.

First supply a rational lift `g` of `x`. The existing
`QuotientConjugacyLift.quotient_eq` proves equality after `q` of `i` and
`(f.hom ≫ i') ≫ inner(g⁻¹)`.
`splitUnipotentKernelCorrection` applies
`QuotientHomCocycle.splitUnipotentTorusConjugator` to these two maps,
with the published affine torsor proof discharging its third proposition
input. This returns an actual rational point `v` of `N`.

`splitUnipotentConjugator` is `g * (v ≫ n)`. Its projection equals `x`
because `v ≫ n` lies in the exact kernel. Its conjugation equation is
`i ≫ inner(g * (v ≫ n)) = f.hom ≫ i'`. The correction conjugates `i`
to the backwards-conjugated second map; composing with `inner(g)`
cancels that backwards conjugation. The order of multiplication agrees
with the existing inner-automorphism convention.

## Represented fppf quotient interface

`QuotientConjugacyLift.fppfSplitUnipotentConjugator` combines the rational
lift above with this correction. Its hypotheses are an affine `G`, a smooth
connected closed subgroup `N` with both `IsUnipotent N` and
`IsSplitUnipotent N`, the supplied fppf quotient `q`, the two structural
propositions, and the specified quotient conjugacy with `f`.
Closedness gives the monic affine subgroup, and the exact quotient
predicate gives the required represented kernel equality.

`fppfSplitUnipotentConjugator_comp` proves that the resulting point maps
to exactly `x`. `fppfSplitUnipotentConjugator_conjugates` proves actual
conjugacy with exactly the supplied source isomorphism `f`.

Finally,
`subgroupConjugate_iff_quotient_of_isTorus_fppf_split_unipotent_kernel`
proves equivalence between `SubgroupConjugate i i'` and
`SubgroupConjugate (i ≫ q) (i' ≫ q)` under those group and structural
hypotheses. The forward direction is postcomposition. The reverse direction
extracts the quotient point and source isomorphism and applies the actual
conjugator construction. It adds no rational-point surjectivity premise.

The provenance is internal composition of the published affine torsor proof,
the affine-test quotient-fiber adapter, the existing inverse-conjugation
identity, and the conditional split unipotent same-source correction.
The smooth connected split kernel remains an assumption. Torus lifting as a
group homomorphism, quotient maximality, and the full maximal-torus
conjugacy theorem remain outside this contribution.
