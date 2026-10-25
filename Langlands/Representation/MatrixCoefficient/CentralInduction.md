# Matrix coefficients in actual smooth induction from the center

Author: Worker 386.

This internal construction is an algebraic precursor to a regular
representation with a prescribed central character. It places actual matrix
coefficients in the existing smooth induced function space. It constructs no
Hilbert space and makes no claim of a discrete-component embedding.

For a topological group `G` and any character
`χ : Subgroup.center G →* ℂˣ`, `Induction.CentralFunctions χ` is precisely
the existing smooth scalar induced carrier from the actual full center,
and `centralInduced χ` is its right-translation representation. The functions
satisfy `f(zg) = χ(z) f(g)` and each has a uniform open right stabilizer.
Neither the definition nor its existence as a possibly zero function space
asserts smoothness or unitarity of an arbitrary character.

When all values of `χ` have norm one, `centralNorm χ hχ f` descends the real
function `g ↦ ‖f(g)‖` to the actual central quotient `G / Z(G)`.
Its well-definedness uses centrality to change right coset representatives
and the existing left covariance. `centralNorm_mk` is the exact value formula.
`centralNorm_isLocallyConstant` descends local constancy from the existing
smooth induction theorem through the quotient topology.
`centralNorm_translate` identifies right translation with multiplication by
the class of the translating group element on that same quotient.
No complex-valued descent of a function transforming by a nontrivial
central character is asserted.

Now let `ρ` be an algebraic complex representation on `V`, let
`c : UnitaryCentralCharacter ρ` be the existing scalar-action datum, and assume
`hρ : IsSmooth ρ`. For every algebraic linear functional `ℓ`,
`c.coefficientIntertwiner hρ ℓ` maps `v` to the actual function
`g ↦ ℓ(ρ(g)v)` in `centralInduced c.character`. The scalar-action law of `c`
proves covariance, and the open stabilizer of `v` fixes this entire
function on the right. Linearity and equivariance follow directly from the
representation and functional laws. Smoothness of `ℓ` is not needed for this
construction.

Evaluation at the identity recovers `ℓ(v)`. Hence a nonzero `ℓ` gives a
nonzero intertwiner. If the source is irreducible, Mathlib's
injective-or-zero theorem for intertwiners shows that this map is injective.
This is an algebraic injection into actual smooth induction; no norm bound,
isometry, completion, or closed-range assertion follows from this theorem.

`coefficientIntertwiner_norm` proves equality with the published
`c.coefficientNorm ℓ v` as functions on the actual central quotient.
`coefficientIntertwiner_memLp_iff` therefore gives an identical integrability
criterion for any measure and exponent. In the square-integrability
application, the existing analytic predicate supplies that criterion for
smooth-dual functionals. This module does not extend it to arbitrary
functionals or Hilbert-completion vectors.

The group and vector carrier universes remain independent. The original
carrier has no topology, norm or finite-dimensionality assumption, and
the construction does not assume irreducibility until the injectivity
theorem. No p-adic or positive-rank specialization is needed.

## Provenance

This is a direct internal derivation from
`MatrixCoefficient.ModuloCenter`, `Induction.CompactQuotientProof` and
Mathlib's irreducible-intertwiner theorem. It retains the existing positive
central character and right-translation conventions, rather than treating
a source's analytic regular-representation assertion as an input.
Hilbert completion, the invariant integrated form, the discrete-component
theorem, and mirabolic restriction remain separate obligations.
