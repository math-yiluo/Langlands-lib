# Existence and denominator independence of rational height

`Langlands.FormalGroup.ModuleLaw.rationalHeightExistenceUniqueness` proves
`RationalHeightExistenceUniquenessStatement`. For each local quasi-isogeny
on an open \(U\), it constructs the unique function \(U\to\mathbb Z\) that
locally equals the height of an integral numerator minus the height of the
source scalar denominator. Both heights are exponents of actual kernel
ranks with base the residue cardinality \(q\) of \(O\).

Harris, *Supercuspidal representations in the cohomology of Drinfel'd
upper half spaces* (1997), Appendix, printed p. 112 (PDF p. 38), describes
rational \(p\)-height by a difference of logarithmic kernel ranks.
Rapoport and Zink, *Period Spaces for p-divisible Groups* (1996),
Definitions 2.6 and 2.8, printed pp. 51–52 (PDF pp. 66–67), give the integral
height and quasi-isogeny conventions. The Lean theorem proves the
derived affine finite-coordinate \(O\)-height statement, with its
\(q\)-normalization specified in the published target.

For existence, pick a local integral numerator isogeny and restrict it to
a basic open around the given point. Base change its finite kernel model
to the residue field of the corresponding prime. The field rank theorem
gives a \(q\)-power for the fibre dimension, which equals the kernel rank
at that prime. Shrink to a smaller basic open using local constancy of
the finite projective kernel rank. The rank of the restricted model is
then the same \(q\)-power throughout that open. A denominator \(\pi^n\)
has the source scalar-power height \(nd\), where \(d\) is the source
height. This gives an actual local height presentation.

For denominator independence, cross-multiply two presentations of the
same rational section by the opposite scalar powers. Equality in the
sheafification gives equality of the restricted rational Hom elements
near each point. Clearing a nonzero scalar in the localized Hom makes the
integral cross-multiples equal after multiplication by that scalar. Over
the DVR the scalar is a unit times a power of \(\pi\). The unit cancels
algebraically, and the power cancels by local surjectivity of the source
scalar isogeny. Kernel composition now identifies the two sums of
numerator and opposite denominator heights, since exponentiation by
\(q>1\) is injective. Their signed differences agree.

The proof applies this comparison on intersections of the chosen
neighborhoods. At a point, define the function to be the signed difference
of the presentation chosen there. The comparison proves that the function
agrees with that difference throughout the presentation's neighborhood.
It also proves pointwise equality with any function satisfying
`RationalSection.HasHeightFunction`.
