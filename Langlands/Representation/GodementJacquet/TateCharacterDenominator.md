# Exact character Mellin denominator

This internal unit derives the abelian Euler denominator from the actual
character shell coefficients. It retains arbitrary p-adic fields, continuous
quasicharacters and supplied topological data.

For an unramified character, the quotient of any two order-one elements is an
integral unit, so the character values agree. The recurrence is therefore the
order-one recurrence with the value at the specified uniformizer as coefficient.
For nonzero conductor it has order zero. Their reverse characteristic
polynomials are exactly `PadicAbelian.lPolynomial`. The exact shell tail proves
these recurrences after any sufficiently large cutoff.

`scalarMellin_character_denominator` proves that multiplication by the specified
`PadicAbelian.lPolynomial` sends every rational continuation of every unweighted
scalar character Mellin integral to a Laurent polynomial. Here “unweighted”
means integral weight one in `scalarMellinIntegral`; the integrand is
`Φ(a) χ(a) |a|^s`, against the multiplicative Haar measure giving integral units
mass one. All Schwartz–Bruhat tests and all their continuations are quantified.

The published `finiteFunctionShellSeries` supplies an order-one element, a
uniform convergence bound, a lower support cutoff and the actual shell-sum
identity. The proof keeps these coefficients and replaces its unspecified
recurrence by `characterShellRecurrence`, moving the upper cutoff to the
maximum of the two natural cutoffs. The published eventual Laurent rationality
theorem then provides a rational function cleared by exactly the abelian
polynomial, with denominator-regular evaluation on a punctured disc.

The normalized absolute value formula and complex-power identities identify
`|a|^s` with `spectralPoint q s ^ ord(a)`. The norm of the spectral point is
`q^(-s.re)`, so a sufficiently far right half-plane lies in both the convergence
disc and the rationality disc. The actual Mellin integral therefore agrees
with the constructed rational function there, including the required
denominator guard. Uniqueness of rational continuation identifies any supplied
continuation with this one and transfers the Laurent clearing witness.

This is a direct internal consequence of the published shell, conductor and
recurrence results. The two spectral helper proofs specialize the helpers in
Worker 656's `OneVariableMellinProof` and Worker 357's `TateScalarMellin`, which
in turn attribute the elementary power argument to Worker 235's
`RamifiedFiniteFunctionMellinProof`. Their attribution is retained. The
character's finite translation span uses the published
`tateCharacter_translationFinite`; it is not an additional hypothesis.

The reverse-polynomial and denominator conclusions cover both conductor
branches, with no condition on the value of the test at zero. This unit does
not construct a test realizing the reciprocal Euler polynomial, prove that it
is the normalized generator, identify the JPSS pair L-factor, or establish an
epsilon comparison or the closed all-field correspondence.

The existing helpers `character_normalizedAbs_cpow`, `character_spectral_threshold` are public so related modules can reuse their unchanged proofs.
