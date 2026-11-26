# Construction of the regular twisted pseudo-coefficient functional

`twistedPseudoCoefficientFunctionalExistence_of_spectrumSplitting` proves
`TwistedPseudoCoefficientSpectralReductionStatement`. Its premise is
`TwistedPseudoCoefficientSpectrumSplittingStatement`. Its conclusion
`TwistedPseudoCoefficientFunctionalExistenceStatement` supplies a regular,
compactly dominated functional with the required twisted pseudo-coefficient
values in ranks at least two. The three universe levels remain free.

The construction follows the functional-extension step of Henniart–Lemaire
(2011), II.5.13, printed pp. 113–114. The premise is on the actual complex
spans of twisted distributions. It combines the spanning input from II.5.10
with the orbit separation used in II.5.11 and II.5.13. For a σ-discrete
series, it supplies a compact open `J`, an orbit span `L` and a disjoint
complementary span `N` whose sum contains every irreducible twisted
character. The latter span comprises the other essentially tempered
characters, the characters of proper inductions and the characters of
irreducibles with zero `J`-fixed space.

First obtain the nonarchimedean local-field structure on the given extension
with its supplied topology. The finite-order continuous entrywise action
provides arbitrarily small compact open subgroups stable under the
inverse action. The unramified characters trivial on the centre form a
finite set, by the determinant-order description. Interpolation gives a
test `f₀` with the desired values on the part of the orbit at the given
central character. This step works with the given twisting isomorphisms,
including the scalars relating choices after transport between equivalent
representations.

Extend `d ↦ d(f₀)` on `L` to a functional `Φ` on all distributions that
kills `N`. This is possible since the quotient by `N` is injective on `L`.
Vanishing on the classes without `J`-fixed vectors gives compact domination.
Vanishing on the proper-induction span makes the functional identically zero
on the induced families from proper block shapes. On a one-block family,
decompose the distribution at the identity unramified character in `L ⊔ N`. An
invariant unramified twist preserves both spaces, so the regularity of `Φ`
follows from evaluating the orbit summand after multiplying `f₀` by the
character. The finite double-coset expansion gives the evaluations required
by `IsSigmaInducedRegularFunctional` for every irreducible admissible
inducing representation.

On the orbit the functional takes the prescribed values by interpolation.
Tempered irreducibles outside that orbit belong to the complementary span
using the identity unramified twist. The conclusion supplies the input to
twisted trace Paley–Wiener. Realization on irreducibles then gives the values
of `IsTwistedPseudoCoefficient` using the same Haar measure.

## Source

G. Henniart and B. Lemaire, *Changement de base et induction automorphe
pour GL_n en caractéristique non nulle*, Mém. Soc. Math. France 124 (2011),
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
II.2.8, p. 69, treats independence of twisted characters. II.4.4, p. 85,
gives the induced operator. II.5.1 and II.5.7, pp. 100 and 105, give the
unramified convention and the conditions on the functional. II.5.10–II.5.13,
pp. 108–114, give the standard-class decomposition and spectral construction.
