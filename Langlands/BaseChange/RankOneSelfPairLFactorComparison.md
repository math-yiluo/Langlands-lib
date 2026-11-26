# The self-pair Euler comparison in rank one

`RankOneSelfPairLFactorComparisonStatement.{u,v,uV,uW}` concerns a finite extension
of bundled p-adic fields with residue degree `f`. Take admissible irreducible
representations of the two `GL₁` groups, each in its own carrier universe.
For the upper action paired with its smooth dual, let `Q_E` be any certified
Rankin–Selberg denominator. Let `Q_F κ` certify the lower pair in which the smooth
dual is twisted by `κ ∘ det`. The characters `κ` range over the supplied finite
set of all characters trivial on the extension norm. The conclusion is
`Q_E.comp (Polynomial.X ^ f) = ∏ κ : X, Q_F κ`, with independent additive characters
and self-dual Haar measures on the two fields.

`rankOneSelfPairLFactorComparison` transports the actions to character models using
`GodementJacquet.exists_tateCharacterModel`. Smooth duality takes a scalar character
`χ` to `χ⁻¹`. On the lower field, the product character for the twisted pair is
`χ * (κ * χ⁻¹) = κ`. On the upper field, it is the trivial character. The
Tate-character formula `rankOneCharacters_isPadicPairLPolynomial` identifies the
certificates on these models with the abelian polynomials. Representation transport
and uniqueness give the same polynomials for the original certificates.
The open kernel of each norm-trivial character gives a continuous quasicharacter
for the abelian comparison. Applied to the trivial quasicharacter,
`prod_lPolynomial_normTwists` gives the identity with the upper variable substituted
by its `f`-th power.

This gives the rank-one instance of `SigmaLiftSelfPairLFactorStatement` because
`IsCyclicAlgebra` supplies finite dimensionality and `IsSigmaDiscreteSeries`
supplies irreducibility of the upper action. Admissibility is already given.
The rank-one computation applies to any such two actions because their individual
scalar characters cancel with their inverses inside the pairs.

The identity is the rank-one self-pair case of Arthur–Clozel, *Simple Algebras,
Base Change, and the Advanced Theory of the Trace Formula* (1989), Chapter 1,
§6.4, Proposition 6.9(i), printed p. 60 (PDF p. 74), with the determinant-twist
convention on printed p. 61 (PDF p. 75). The retained source ID is
`arthur-clozel-1989-base-change` and its SHA-256 is
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
The implementation uses the Tate denominators directly.
