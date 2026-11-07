# Unramified finite epsilon factors at conductor zero

Worker 1692, internal derived support for the actual Hecke functional equation.
The module uses the existing fixed-Haar epsilon expression without changing its
spectral convention.

For an arbitrary supplied p-adic topology, the published Fourier normalization
theorem and the intrinsic Fourier-squared property of a supplied `SelfDualHaar`
give integer-ring volume one when the actual additive conductor is zero.
Unfolding the existing epsilon expression then gives value one at every complex
parameter when the actual multiplicative conductor is also zero. Self-duality
is required of the supplied measure; the result does not replace it by a chosen
measure.

This is the conductor-zero specialization of Tate, *Number theoretic background*
(1979), section 3.2, (3.2.6.1), printed p.13. The volume normalization follows
Weil, *Basic Number Theory*, second edition (1973), VII.2, Corollary 3, printed
p.108: the self-dual integer-ring volume is `q^(-n/2)`. The implementation reuses
the published exact normalization theorem. It does not rely on the erroneous
sign in Tate's scalar-measure sentence after (3.6.2), printed p.17.

`selfDualHaar_integerRing_eq_one` converts the supplied measure's intrinsic
Fourier-squared identity on Schwartz–Bruhat functions into the raw Fourier
identity used by `LocalFactors.padicFourierNormalization`. The intrinsic
additive-conductor specification supplies that theorem's greatest-level
hypothesis at level zero. Its self-dual volume criterion then simplifies to
volume one. `epsilon_eq_one_of_conductors_eq_zero` unfolds `epsilon` and
`epsilonAt`; the uniformizer power and exponential become one, and the
integer-ring mass has real value one. This retains the supplied measure and
the exact existing spectral convention, for every spectral parameter and
arbitrary universe.

At an actual finite completion, `mem_localIntegers_iff` identifies membership in
the local conductor's integer ring with membership in the completed integer
ring. It uses the published equivalence between the supplied valuative relation
and the completion valuation. Consequently,
`multiplicativeConductor_eq_zero_of_isUnramifiedAt` transports unramifiedness of
an actual Hecke character to zero intrinsic multiplicative conductor: a local
unit of valuation one and its inverse both lie in the integer ring.

`finiteEpsilon` is the expression under the same name in
`HeckeGlobalFunctionalEquationStatement`, made callable with explicit arguments.
Its local characters and self-dual Haar measures are all supplied, and the
topology and Borel measurable structure agree with the global target.
`exists_finset_finiteEpsilon_eq_one_of_additiveConductor` assumes an explicit
finite set outside which the supplied additive conductors are zero. It takes
the union with the published finite ramification set of the Hecke character,
applies the conductor bridge, and uses the local epsilon lemma at each
remaining place and every complex parameter.

These are derived support constructions and lemmas for the global proof.
The last theorem does not establish that a global additive character has
conductor zero almost everywhere: that hypothesis remains explicit.
It also makes no claim about Euler products, meromorphic continuation,
archimedean presentations or the global functional equation.
