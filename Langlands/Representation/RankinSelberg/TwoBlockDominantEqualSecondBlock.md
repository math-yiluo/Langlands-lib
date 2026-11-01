# The actual reversed first-block law at equal rank

This is an internal deduction from the existing first-block Laurent theorem,
ordinary Jacquet realization, reversed-dual section equivalence, and lower
Fourier transport. It packages the two first-block equations for the actual
lower induced model and the same fixed reversed section. It does not assert
either final dominant-rank gamma or L proposition.

The field has its canonical p-adic structures. The test representation has
rank `t + 1`, the blocks have ranks `m i + 1`, and their sum is `t + 1`.
The field, test carrier, and dependent block carriers retain independent
universes. Full Whittaker type is used throughout the existence theorem;
irreducibility is not assumed. Canonical unipotent Haar measures are required
to be right invariant at ranks `t + 1` and both block ranks.

## The fixed ordinary dual realization

`determinantComplexPower_weylLong` uses the published absolute-value identity
for the long Weyl representative to prove that every complex determinant
power evaluates to one there. Consequently
`secondDual_oppositeTwistFunctional_val` identifies the underlying linear map
of each deformed block's second-dual functional with that of its base
second-dual functional. This is equality of linear maps, not a proportionality
chosen after the tests.

`exists_equalFirstBlockBound_forOrdinaryFunctional` adapts the original
first-block assembly to any representation family equal to the opposite
twist and any block functionals with the same underlying base linear maps.
The supplied induced functional must realize the ordinary Jacquet function
at every section and group element. The proof substitutes the representation
family, identifies the subtype functionals, and derives the smaller-pair
epsilon equation from `unequalRankFunctionalEquation`; the strict smaller
rank follows from the two positive block sizes. The published Laurent law
then gives normalized polynomial generators and its coefficient identity.
`unfoldedJacquetSeries_eq` identifies the ordinary upper series with the
actual coefficient model of this very supplied functional. No nonzero or
separately chosen dual induced functional is needed in this lemma.

`reversedDualSectionEquiv_ordinary` proves ordinary realization for the
specific `reversedDualSectionEquiv` already used by the Fourier law. It
transports the original induced functional using
`transportedSecondDualFunctional`. Its coefficient is the actual
Weyl-translated inverse-transpose coefficient. The original ordinary
realization and the Jacquet identity of `twoBlockDualSectionJacquet` then
identify it with the reversed ordinary integral. Surjectivity is used by
applying that identity to `E.symm fD`, so this holds for every reversed
section, rather than only a separately selected image.

## One bound and three actual laws

`exists_reversedEqualFirstBlockBound` applies the generalized bound to the
complete reversed inverse-transpose family: sizes, carriers, representations,
and functionals are all reversed. The test is its first dual at the character
`psi.scale (-1)`. Full type and nonzero functionals are transported by the
published duality lemmas. `reversedDual_oppositeTwistBlocks` identifies this
family with the opposite twist of the base reversed family at the same real
parameter `u`; the linear-map identity above identifies its block
functionals. The fixed ordinary dual-realization lemma discharges the last
Jacquet-realization premise. `negatedSelfDualHaar` retains exactly the supplied
additive measure and gives its inverse-character self-duality certificate.

`EqualTwoSidedFirstBlockLaws` is a proposition containing the original
`EqualFirstBlockCoefficientLaw`, its reversed version for the functional
transported through that same fixed `E`, and
`EqualLowerFourierCoefficientLaw`. Each first-block law contains its complete
smaller-pair epsilon equation, a scalar for the central minus-one action,
normalized polynomial generators, and an identity common to all sections,
model coefficients, and row tests. These witnesses may depend on the
compatible quotient measures. The Fourier clause contains its actual
integrability equivalence and complex and raw-norm coefficient identities,
with the prescribed determinant-slice reflection and factor `q^(-k)`.

`exists_equalTwoSidedFirstBlockLaws` takes the maximum of the original and
reversed bounds. At every larger real `u`, the original theorem supplies
absolute convergence of every ordinary Jacquet section and a nonzero
ordinary realizing functional `Ju`. This single `Ju` precedes all compatible
large and two small quotient measures. For each such triple the proof combines
the original law, the reversed law for the transported `Ju`, and the actual
fixed-section Fourier law. Nonzero test and base block functionals are
explicit hypotheses; no analytic identity or induced full-type hypothesis
is added.

This result still concerns sufficiently large real opposite twists at equal
rank. Ordinary Jacquet convergence is distinct from integrability of every
lower quotient slice; the Fourier clause gives an equivalence for those
slices. Finite numerator assembly, continuation to the undeformed family,
the strictly dominant case, and the symmetric final gamma and L certificates
remain separate obligations.
