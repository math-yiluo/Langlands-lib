# Rational-locus stabilizers on a fixed quotient algebra

Author: Worker 36.

This derived construction packages the setwise stabilizer of an actual
unit-radius rational locus as a subgroup of the bounded automorphisms of its
presented strict affinoid base algebra. It then constructs a homomorphism from
that subgroup to the bounded automorphisms of the fixed rational quotient
algebra. No equality of chosen presentations is required.

The spectrum action uses inverse algebra pullback. `locusStabilizer d` consists
exactly of the operators whose point-action image of `d.locus` equals
`d.locus`. Membership therefore identifies the moved presentation's locus with
the original locus, using the published `locus_smul` identity. This does not
require that any individual spectrum point be fixed.

Over a complete ultrametric normed scalar field, `stabilizerInclusion` is the
inclusion from the original rational object into its moved presentation.
`stabilizerSectionMap` first uses the published forward quotient comparison,
then restricts along that inclusion. It is an actual bounded algebra endomorphism
of `d.algebra`. Its equation on `d.baseMap` is the forward base-algebra operator.
The uniqueness theorem for maps out of the rational quotient proves the identity
and multiplication laws by checking those equations on the base. Applying the
multiplication law to an operator and its inverse constructs
`stabilizerSectionAut`; the same laws give the group homomorphism
`stabilizerSectionAction`. Multiplication composes functions with the right
factor acting first. The final theorem states compatibility on each base section.

The subgroup definition and locus identity need no completeness assumption.
The section maps use the already proved rational representation and hence retain
completeness of the scalar field. Zero and nonreduced quotients, empty rational
loci, empty numerator tuples, and trivial valuations are permitted. The module
does not choose a topology on the automorphism group or prove openness of the
stabilizer or parameter continuity of its section operators. Those are separate
obligations. It also does not assert sheaf descent or construct full analytic
spaces or equivariant etale sites.

The geometric provenance is Berkovich, *Non-archimedean analytic spaces*, Trieste
lectures (2009), Definition 2.1.11, p. 8, and Definition 2.2.1 and Exercise
2.2.2(ii), p. 9. These give the contravariant bounded-map category and the
representing property of rational domain algebras. The stabilizer subgroup and
its fixed-quotient action are derived here from those constructions and the
Library's proved rational comparison and restriction laws; they are not quoted
as separate numbered claims of the source. Registered source
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
