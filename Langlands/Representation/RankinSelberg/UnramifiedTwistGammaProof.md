# Complete symmetric unramified gamma spectral transport

`Langlands.RankinSelberg.unramifiedTwistGamma.{uF,uV,uW}` proves the unchanged
published `UnramifiedTwistGammaStatement` with independent field and two carrier
universes. For either member of the supplied pair, twisting its actual action
on the original carrier by the supplied character `χ(x) = |x|ᵘ` transports the
complete symmetric gamma certificate by
`rationalRescale (spectralShiftUnit q hq u)`, where `q` is the canonical
p-adic field's actual residue cardinality.

The proof assembles the internal transport lemmas in the paired
`UnramifiedTwistGammaScalar`, `UnramifiedTwistGammaIntegrals`,
`UnramifiedTwistGammaCertificates`, and `UnramifiedTwistGammaAssembly` modules.
The two determinant characters have product |·|ᵘ and are separately trivial
on −1; choosing either character to be trivial gives the two twist positions.
The coefficient identities use common original carrier vectors. The forward
integral shifts by `+u`; inverse transpose gives the actual dual integral the
shift `-u`, including its complementary block and right Weyl translation.
Determinant signs have norm one, so the same model minus-one scalar survives.
The scalar rational identity checks reduced denominators and uses
`1 - s - u = 1 - (s + u)` for the reflected dual argument.

The fixed-functional transport preserves a nonzero rational witness by
injectivity of rational rescaling, retains the same equal-rank Fourier partner
and test data, and treats every unequal-rank rectangular decomposition.
The complete-factor assembly keeps the supplied compatible-measure existence
certificate and the nonzero functionals. Its universal clause takes arbitrary
compatible measures and arbitrary nonzero functionals of the twisted actions,
untwists their underlying linear maps, and applies the original certificate.
Thus no choice of a selected functional replaces a universal quantifier.

`UnramifiedGammaTwist.pair_factor` separates strict inequality, equal rank,
and the impossible larger test rank. `pair_both` specializes one of the two
determinant characters to the trivial character, producing both twist
positions. `padic_pair_both` installs precisely the field's canonical data,
and `padic_symmetric_both` reads the larger rank first, swapping the two
conclusions in the reversed branch. The final theorem applies this result to
the supplied self-dual Haar measure.

This is an internally derived transport theorem for the Library's existing
JPSS definitions, rather than an initial gamma-factor existence theorem.
Its conventions come from Jacquet–Piatetski-Shapiro–Shalika,
*Rankin–Selberg convolutions* (1983), registered source
`jpss-1983-rankin-selberg`, equations (2.4), printed p.387, (2.7)(iii),
pp.390–391, (2.12), p.403, and (3.1), pp.404–405. The proof uses no irreducibility or
Whittaker-type assumption and no adjacent-rank or other multiplicativity
result.
