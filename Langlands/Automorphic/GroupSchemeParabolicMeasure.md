# Mass-one measures for the intrinsic rational parabolic radical family

For an actual affine connected reductive group over any number field, this
module constructs the measure family needed by the canonical
all-proper-parabolic constant terms. Local finite type is retained
explicitly for the existing adelic Haar APIs. The algebraic existence
premise `ParabolicDynamicStatement` remains explicit.

A represented parabolic radical has closed adelic image: both the
parabolic embedding and radical embedding are closed, their composite is
closed, and the public closed-immersion theorem on actual affine points
applies. This proof also supplies the radical's affineness. Combined with
the preceding compactness theorem, every canonical radical's actual
adelic subgroup is locally compact and its actual rational quotient is a
compact Borel space.

`properParabolicHaarMeasure` and `properParabolicQuotientMeasure` use the
intrinsic subgroup Haar and rational quotient constructions of
`AdelicSubgroupHaarMeasure`. The same inverse quotient mass scales both
measures. In particular, every quotient measure is proved to be a
probability measure. This implements the mass-one unipotent quotient
normalization of Mœglin–Waldspurger, *Spectral Decomposition and
Eisenstein Series* (1995), I.1.13, printed p.18, first paragraph, at the
stated number-field radical scope. The measure is defined on the actual
subgroup and quotient, independently of a presentation used to prove
closedness and compactness.

`normalizedParabolicCuspidalSubrepresentation` specializes the earlier
all-proper continuous vanishing construction to this actual measure
family. Compactness, continuity of the descended integrand and
probability finiteness prove absolute convergence for every continuous
rational-invariant ambient function. Membership is exactly vanishing of
these normalized integrals at every ambient adelic argument and every
proper rational parabolic, as in Getz–Hahn Definition 6.5.1 and (6.18).
The positive ambient right action is inherited from the preceding
subrepresentation.

Exact complex Weil compatibility with counting measure on the actual
principal image, and left radical invariance of the constant term, retain
the explicit analytic right-invariance premise on actual subgroup Haar.
These assertions reuse the scaled compatibility and quotient translation
theorems; no algebraic determinant is treated as an analytic modulus.
The unit does not prove this remaining unimodularity premise, independence
from changing the initial Haar normalization, standard-parabolic
reduction, Levi automorphic mapping properties, or full almost-everywhere
cuspidal L² identification.
