# Local self-pair Euler comparison from cyclic globalization

`sigmaLiftSelfPairLFactor_of_globalization` proves
`SigmaLiftSelfPairFromGlobalizationStatement`. It takes four propositions as
premises. These give ordinary discrete-series globalization, cuspidal base
change in arbitrary cyclic degree, uniqueness of an irreducible local σ-lift
and the completed global Rankin–Selberg equation. Its conclusion is
`SigmaLiftSelfPairLFactorStatement` for bundled finite extensions of `ℚ_p`
with independent field and action universes. The supplied actions, lift
relation, additive characters and certified polynomials are those of that
statement. The rank-one and degree-one cases follow from the corresponding
local polynomial comparisons.

For higher rank and nontrivial degree, `cyclicGlobalizationWithSplitPlaces`
realizes the local extension at a unique upper place and supplies two
distinct split auxiliary places. The field isomorphism transports the
square-integrable lower action by change of variables on the central
quotient. The ordinary globalization premise realizes it up to an
unramified determinant twist, with supercuspidal components at the two
auxiliary places. The global lifting premise supplies the upper cuspidal
presentation and an actual distributional lift on the distinguished
completion tensor. `distinguishedTensorLiftTransport` transfers it to the
upper field completion. `distinguishedSigmaLiftMatch` uses uniqueness to
identify the upper completion action with the norm twist of the given
σ-lift.

For each global presentation, the second member of the pair is its actual
cuspidal contragredient. The finite local compatibility of those
contragredients gives their smooth duals at the distinguished places.
Outside the exceptional sets, the dual Satake spectra are the inverses of
the forward spectra, so the same residue-degree power relation holds on the
dual presentations. `distinguishedNormCharacters` gives the global norm
characters with their restriction multiplicities at all places and gives
an explicit bijection with the supplied local family at the distinguished
place.

At either distinguished completion, the first member of the forward pair
has the globalization twist times the chosen character, and the second has
the inverse globalization twist. The corresponding dual pair has the
inverse chosen character on its first member. Opposite determinant twists
preserve the full normalized polynomial certificate, and moving a twist to
the second member also preserves it. Together with the generic class-to-action
comparison and field transport, this identifies the forward certified
polynomials with the polynomials in the local statement. The forward root
bound comes from `temperedSelfPairEulerRootRegion`. For the dual factors,
`analyticTemperedLPolynomialData` supplies an actual pole-free certificate
for the smooth dual paired with the original action twisted by the inverse
norm character. The same transport identifies those denominators with the
dual factors of the completed equations.

`cuspidalPairDistinguishedNormEuler` now compares the actual completed
equations after matching all finite factors away from the distinguished
place. Compatibility with the cardinalities of the completed residue
fields identifies the inertia degree used there with the supplied residue
degree. Reindexing the product by the bijection of characters gives the
identity for the original local polynomials.

The comparison follows the globalization and localization in Henniart and
Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle* (2011), II.6.18–II.6.19, printed pp. 132–134
(PDF pp. 140–142), with the self-pair specialization in II.4.12, printed
p. 96 (PDF p. 104). The retained copy is registered as
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
The characteristic-zero pair formula is Arthur and Clozel, *Simple Algebras,
Base Change, and the Advanced Theory of the Trace Formula* (1989), Chapter 1,
Proposition 6.9(i), printed pp. 60–61 (PDF pp. 74–75). The retained copy is
registered as `arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
