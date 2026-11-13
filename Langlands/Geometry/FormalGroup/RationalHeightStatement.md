# Existence and denominator independence of rational height

`RationalHeightExistenceUniquenessStatement` is an unproved proposition
target for the canonical formal O-height function.

Harris, *Supercuspidal representations in the cohomology of Drinfel'd
upper half spaces* (1997), Appendix, printed p.112 (PDF p.38), defines the
height of a quasi-isogeny as the difference of the logarithmic ranks
of its numerator kernel and source scalar-power kernel, and states
that this is a locally constant integer-valued function. His
quasi-isogeny definition cites Rapoport–Zink, *Period Spaces for
p-divisible Groups* (1996), Definition 2.8, printed p.52 (PDF p.67);
the integral height normalization is at Definition 2.6 and the
following paragraph, printed p.51 (PDF p.66).

This target is the derived affine finite-coordinate O-height analogue,
rather than Harris's literal p-height formulation. O is a discrete
valuation ring with finite residue field, F is its fraction field,
and π is irreducible in O, hence a uniformizer. The rank normalization
is the actual residue field cardinality `Nat.card`, not a freely
chosen q. R is an O-algebra. The formal modules M and N have finite
coordinate sets and the previously defined finite O-heights d and e:
π is nilpotent on the base, the actual point functors are π-divisible,
and every scalar-power kernel has its required finite projective
representation and rank.

For any open U and any actual `LocalQuasiIsogeny F π M N U`, the target
requires a unique function h from U to the integers satisfying
`RationalSection.HasHeightFunction`. That relation requires local
scalar-denominator presentations with actual constant ranks for
both the numerator and source scalar kernels, and identifies h with
their signed height difference. Its already implemented elementary
properties imply that such an h is locally constant.

The existence assertion must supply these local rank presentations
from the local quasi-isogeny condition. Uniqueness must show that
different exponents and integral representatives yield the same
signed rank difference. Neither assertion is an assumption of the
formal modules or of the quasi-isogeny type.

There is no proof in this module. The target does not identify the
O-height normalization with Harris's p-height, prove additivity under
composition, treat varying coordinate atlases, construct a moduli
functor or assert representability.
