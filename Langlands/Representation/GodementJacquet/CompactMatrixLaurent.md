# Laurent integrals of compactly supported matrix functions

This derived helper implements the elementary compact-support step in the
Godement–Jacquet argument, Section 5, printed pages 69–70 of *Zeta Functions
of Simple Algebras* (1972), registered as
`godement-jacquet-1972-zeta-simple-algebras`.

A continuous integer-valued order has finite image on the compact topological
support of a function. The weighted integral is consequently a finite sum of
integrals on order fibers. Each coefficient is the actual Haar integral of
the function on a fiber. The definition `discreteWeightLaurent` forms this
Laurent polynomial for any specified finite set of orders. With a finite set
containing every order in the support, the following theorem proves
absolute convergence and the exact evaluation formula for every complex
spectral parameter. The generic lemma uses any Borel measure finite on compact
sets, and needs no representation or group structure on its domain.

The matrix specialization uses the canonical topology, normalized absolute
value, residue cardinality and general-linear Haar measure. The exact
published determinant-weight formula identifies its exponent with the integer
order of the determinant. An arbitrary fixed complex shift is absorbed into
the continuous compactly supported function. No coefficient support or
convergence conclusion for a general full-matrix test is asserted here.

For a full-matrix test and a continuous coefficient whose product has compact
support on the general linear group, the corollaries give the exact shifted
matrix integral at every parameter. They then construct
`HasShiftedRationalValue` with a convergence threshold of zero, using regularity
of Laurent rational functions at the nonzero spectral point. Finally,
uniqueness of rational continuation shows that every rational value of that
same product is in the image of the Laurent-polynomial embedding.

This proof is a finite discrete-order partition, rather than the source's
finite compact-open coset partition. The compact-support premise is explicit
in this helper and must be discharged before applying it in the closed
supercuspidal functional-equation proof.

The canonical local instances have explicit module-specific names so this helper
can be imported together with the matrix analytic-data interfaces. Their
definitions, all mathematical declarations, and all hypotheses are unchanged.
