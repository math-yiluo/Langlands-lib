# Rational height presentations from actual kernel ranks

Harris, *Supercuspidal representations in the cohomology of Drinfel'd
upper half spaces* (1997), Appendix, printed p.112 (PDF p.38), defines the
height of a quasi-isogeny φ by subtracting the logarithmic rank of the
kernel of p^n on its source from the logarithmic rank of the kernel of
p^nφ. He states that this is a locally constant integer-valued function.
Rapoport–Zink, *Period Spaces for p-divisible Groups* (1996), Chapter 2,
Definition 2.6 and the following paragraph, printed p.51 (PDF p.66),
give the integral kernel-rank normalization.

This module formulates the local rank relation on the actual rational
Hom sheaf constructed earlier. It uses a distinguished scalar π in O,
its image in the O-algebra field F, and a natural number q as the rank
normalization. For Harris's p-height these specialize to p and p. The
formal O-height normalization instead uses a uniformizer and the residue
field cardinality. No identification between these normalizations is
asserted.

`RationalSection.HeightPresentation π q z` consists of an exponent n,
an actual integral formal homomorphism f representing π^n z, and
natural numbers a and b. It requires f to have actual isogeny height a
and multiplication by π^n on the source to have actual isogeny height b.
Thus both kernels are represented finite locally free point kernels
with constant ranks q^a and q^b. The signed `index` is the integer a − b.
The denominator contribution is the rank of the source scalar kernel,
without assuming a preassigned height for the source.

Coherent coefficient restriction preserves integral heights, including
the source scalar-power height. This uses base change of the actual
finite kernels and the identity-coordinate comparisons already used
for integral Hom. A height presentation therefore restricts to any
smaller open, with the same index.

`RationalSection.HasHeightFunction π q z h` requires a neighbourhood of
each point on which a height presentation exists and h is its index.
The implemented proof obtains local constancy directly from these
neighbourhoods. It also proves the local scalar-isogeny condition and
preserves the height relation under restriction. `locallyConstant`
packages a function satisfying the relation as a locally constant map.

The provenance is a derived finite-coordinate affine formulation of
Harris's rank difference. The ring O is any commutative ring; F and R
share a universe, and O may have a different universe. These definitions
apply to the existing fixed global coordinate laws. A function h is
constrained by the actual local kernel ranks; it is not supplied as an
unconstrained height datum.

Existence and uniqueness of a height function for every local
quasi-isogeny, independence of the chosen exponent and representative,
and additivity under composition remain unproved. In particular this
module defines the height relation and its elementary properties; it
does not yet assign a canonical height map to all quasi-isogenies or
assert representability.
