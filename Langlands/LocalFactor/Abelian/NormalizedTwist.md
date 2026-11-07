# Normalized character twists and spectral abelian epsilon

Worker 1555 derives this internal comparison from the constructed actual
conductors, the continuous normalized absolute-value power character, and
the existing fixed-Haar abelian epsilon expressions. No original-literature
assertion or functional equation is added.

The normalized power character is trivial on integral units: their valuation
is one, their order is zero and their normalized absolute value is one.
Multiplication by any actual unramified character therefore preserves
triviality on every principal-unit group, including level zero. Applying the
least-conductor characterization in both directions proves equality of the
actual conductors. The normalized absolute-value power is a special case.

Its value on the specified uniformizer is exactly the existing spectral
variable `exp(-s log q)`. The normalized character constructor uses that value,
and the specified uniformizer has order one.

`epsilonIntegrand_normalizedAbsPower_mul` proves an equality on every field
element between the unshifted plus-sign epsilon integrand for
`normalizedAbsPowerCharacter s * chi` and the existing spectral Gauss
integrand for `chi` at `s`. At zero both are zero. At a nonzero element the
inverse of the power character contributes `exp(-s log |x|)`, as required by
the existing Gauss integrand.

`epsilon_normalizedAbsPower_mul_zero` proves the corresponding equality
of the actual epsilon expressions. The conductor equality gives the same
branch and the same compact shell. In the ramified branch the integrands
agree. In the unramified branch multiplication of exponential factors gives
the original additive-conductor factor at `1 - s`, with the same actual
integer-ring Haar volume.

`abelianEpsilonExpression_normalizedAbsPower_mul` combines this equality
with the published identification of the spectral epsilon expression at zero
with the measure-dependent abelian expression.
`NormalizedTwistEpsilonStatement` quantifies this comparison over every prime,
every finite p-adic field and supplied topological data, every continuous
quasicharacter, every nontrivial unitary additive character, every actual
regular additive Haar measure and every complex parameter. The included
proof applies the preceding comparison.

No self-duality, measure existence, Gauss nonvanishing or functional equation
is needed for these identities. They do not construct a reciprocity family,
a local-constant system, an analytic JPSS comparison or the closed
supercuspidal correspondence.
