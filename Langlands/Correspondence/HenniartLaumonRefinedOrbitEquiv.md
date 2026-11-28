# Refined orbit equivalence from Laumon's twist-equivariant rank shift

`ladicRefinedStratumEquiv` sends an orbit of a fixed Swan exponent
and torsion number to its orbit under an \(\ell\)-adic class bijection
that commutes with unramified twists. For each twisting character,
injectivity gives the same fixed-class condition in both ranks.
The two maps from the source classes of the given torsion number
onto their respective orbit strata are surjective. Equivariance and
injectivity give the same fibers, yielding the orbit equivalence.

`laumonNumericalReduction_of_refinedOrbitEquiv` applies this to
the two inputs of `LaumonNumericalReductionStatement`. Choose a
prime \(\ell\) larger than the residue characteristic and a coefficient
embedding into \(\mathbb C\). The orbit comparison identifies both
refined strata with their complex Weil counterparts by an injective
image map. Extended cardinalities therefore agree, giving
`LaumonNumericalStatement`. [Numerical reduction](HenniartLaumonNumericalReductionStatement.md)

The argument follows `henniart-1988-numerical`, SHA-256
`3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`,
§4.3, printed p. 510 (PDF p. 15), where the local Fourier rank shift
gives equality of the unramified-twist counts.
