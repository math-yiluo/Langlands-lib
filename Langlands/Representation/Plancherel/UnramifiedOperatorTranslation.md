# Translation of actual unramified operator parameters

This is derived algebra for the polynomial and rational families of Waldspurger
IV.1, printed pp.276–277 / PDF pp.42–43 of
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The source uses the evaluation polynomials `b_g(χ) = χ(g)`, finite expansions in
fixed vectors, one denominator for the whole operator family, and extension to
that denominator's nonzero locus. The present construction proves their
compatibility with translating the actual character parameter. This is a
prerequisite for comparing different choices of orbit base point; the module
does not perform that representation-theoretic comparison or orbit descent.

## Character and regular-algebra translation

Let `G` be any group with a topology, and let `ν` be any family of positive
real unit-valued group characters. The module uses the existing full
`unramifiedCharacters ν` and evaluation-generated complex subalgebra
`unramifiedRegularFunctions ν`. The group and character-index types have
independent universes. No local-field, reductivity, commutativity of `G`,
finite-generation or separation hypothesis is needed for these constructions.
There is no new claim identifying this algebra with the coordinate ring of an
algebraic torus.

For `τ` in this actual character space, `unramifiedParameterTranslation ν τ`
is the homeomorphism `χ ↦ τ * χ`, with inverse `χ ↦ τ⁻¹ * χ`. The topology is
the existing subspace topology on continuous characters. The compact-open
function-space group topology supplies continuity of multiplication and inverse.

`unramifiedRegularTranslation ν τ` is the complex algebra automorphism

`T_τ(b)(χ) = b(τ * χ)`.

On an evaluation generator it satisfies
`T_τ(b_g) = τ(g) • b_g`. The private ambient function-algebra automorphism
preserves the regular algebra because every translated generator belongs to it:
apply the universal property of algebraic adjoining and closure under complex
scalar multiplication. Translation by `τ⁻¹` gives the inverse automorphism.
The evaluation and inverse evaluation formulas are proved explicitly.

For any subset `Ω`, `unramifiedTranslationPreimageEquiv ν τ Ω` restricts
parameter translation to a bijection `T_τ⁻¹(Ω) ≃ Ω`. Its forward and inverse
formulas use `τ * χ` and `τ⁻¹ * χ`. Here `T_τ⁻¹(Ω)` denotes the set preimage
under the forward parameter map, not a direct image or a choice of inverse
branch. No openness of `Ω` is required.

## Polynomiality and whole-operator rationality

Source and target vector spaces have independent universes and arbitrary
complex module structures. They need no topology or finite dimension.
The three equivalences in `UnramifiedOperatorFamily` compare the pullback on
`T_τ⁻¹(Ω)` with the original family on `Ω`:

- `isPolynomialOn_translation_iff` translates every regular coefficient in a
  finite fixed-vector expansion; translation by `τ⁻¹` gives the converse.
- `isPolynomialOperatorOn_translation_iff` applies that argument to the image
  of each fixed input vector.
- `isRationalOperatorOn_translation_iff` translates the one regular denominator
  chosen before quantifying over input vectors. Its nonvanishing condition is
  transported by the subset bijection, and the cleared polynomial operator is
  transported by the preceding equivalence. The converse uses the inverse
  regular-algebra automorphism. Thus no vector-dependent denominator is
  introduced.

These are equivalences for arbitrary subsets, including empty subsets; no
analytic uniqueness or density result is used.

## Translation of supplied continuation data

Given existing `RationalOperatorContinuationData Ω A`, its `translation τ`
contains precisely the translated denominator `T_τ(p.denominator)` and the
globally linear numerator `χ ↦ p.numerator (τ * χ)`. Each finite expansion of
the original numerator is pulled back by translating its regular coefficients,
while retaining its fixed vectors. The original clearing equation and
denominator nonvanishing prove the translated record's corresponding fields.

`translation_regularRegion` proves that the new regular region is exactly
the preimage of the original regular region. `translation_continuedOperator`
identifies the new continued operator at `χ` with the original continued
operator at `τ * χ`. These identities follow directly from the denominator,
numerator and inverse-scalar definition of continuation. They neither enlarge
the region nor assign values at denominator zeros.

## Provenance and remaining obligations

The source provides the evaluation-polynomial and common-denominator notions;
the translation automorphisms and transport arguments here are elementary
derivations using those notions and the existing character topology and
continuation records. No external representation or analytic theorem is
assumed. The constructions apply to the actual rational norm-character family
of a general reductive group by specialization, in arbitrary characteristic.

Supplied continuation data remain a premise. Actual twist and induction
compatibility when the inducing representative changes, naturality of the
original standard integrals, stabilizer invariance and descent to representation
orbits remain separate obligations. This module does not prove standard-integral
convergence or rationality, generic induced irreducibility, parabolic
independence, nonvanishing or positivity, the source-normalized global `j` or
`mu`, or a Plancherel theorem.
