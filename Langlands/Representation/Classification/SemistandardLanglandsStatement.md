# Semistandard recovery of Langlands data

This module states `Langlands.GLSemistandardLanglandsConjugacyStatement`,
a derived specialization of Silberger 1978, Corollary 6.2, printed p.103, to
positive-rank `GL_n` over the project's p-adic fields. It is an unproved
proposition definition; it supplies no proof of the corollary.

## Actual data and hypotheses

The fixed maximal split torus `A₀` is the actual split component of the standard
singleton block shape: the subgroup of invertible diagonal matrices. A
`ConjugateBlockPair P` consists of an ordered positive block shape and a matrix
`c`. Its actual parabolic, split component and Levi are the conjugates by `c`
of the corresponding standard subgroups. The input condition
`P.splitComponent ≤ A₀` is the semistandard condition from S78 p.95.
It does not provide a Weyl element standardizing the pair.

The representation `σ` is expressed in the product-Levi coordinates of `P`.
Thus its corresponding action on the actual Levi is obtained using the inverse
of the injective coordinate embedding `m ↦ c diag(m) c⁻¹`. The representation
`τ` is expressed in the coordinates of the standard block shape `B`. Both are
irreducible and analytically tempered on their entire product Levi. The reused
`IsLeviTempered` predicate quantifies over every Borel Haar measure on the actual
central quotient and uses `IsTemperedModCenter`, including admissibility and
unitary central character. Haar-measure existence for this topology is proved
in `TemperedInductionStatement`, so the quantifier is nonvacuous. No tensor
factorization, cuspidal support or classification data are assumed.

The determinant exponent vectors `t` and `u` are strictly decreasing in their
respective ordered block coordinates. Transport by `c` sends the standard
positive chamber to the chamber relative to `P`; thus `StrictAnti t` describes
the source's regular positive chamber even when the actual parabolic is not
standard. All real central directions are allowed. For a single block the
regularity condition is vacuous. Weak inequalities and equal-exponent grouping
are not included.

`J` and `K` are arbitrary irreducible representations equipped only with the
existence of actual surjective intertwiners from the two specified inductions.
They are assumed equivalent. The field, two inducing carriers and two quotient
carriers have independent universes `uF`, `uV`, `uW`, `uJ`, `uK`. The actual
function spaces have universes `max uF uV` and `max uF uW`.

## Induction and normalization

The semistandard induction is the actual function-space construction
`T.normalizedConjugateParabolicInduced P`, applied to
`T.leviRealPowerTwist P.shape t σ.ρ`. It uses right translation and the covariance

`f(p x) = δ(P.shape)^(1/2)(projection(p)) · σ_t(projection(p)) f(x)`,

where `projection(p)` extracts the standard Levi coordinates of `c⁻¹ p c`.
The modulus is the transported positive half of the published upper block
modulus. The standard induction of `τ_u` uses the same convention. This statement
does not posit an equivalence of these two inductions as a hypothesis.

The real character on a product Levi is
`∏ᵢ |det(mᵢ)|^(tᵢ)` with the residue-normalized `q^(-valuation)` absolute value.
The source parameter `-iν` therefore gives this positive determinant twist.
On block scalars it is `∏ᵢ |aᵢ|^(sizeᵢ * tᵢ)`. The source Weyl action on `ν`
is expressed below by transport of this actual character. This keeps the
block-size weights, the central direction and the sign of the twist.

## Conclusion

The conclusion supplies a permutation `w`, its actual permutation matrix `y`,
and a continuous multiplicative equivalence `e` between the two coordinate
Levis. It asserts all of the following:

- `y` normalizes the fixed actual torus `A₀`.
- Conjugation by `y` sends the actual parabolic, split component and embedded
  Levi of `P` to those of the standard shape `B`.
- `e` is this specific matrix conjugation in Levi coordinates:
  `diag(e(m)) = y · (c diag(m) c⁻¹) · y⁻¹`.
- Pullback by `e⁻¹` sends the real character with exponent `t` to the one with
  exponent `u`.
- The same pullback sends the untwisted representation `σ` to a representation
  equivalent to `τ`.

In particular, the coordinate equivalence is a conclusion with its actual
embedding law, not an arbitrary comparison assumed in the input. The parabolic
and split-component equalities recover the whole pair; a Levi-only association
would omit source content.

## Source correspondence and derived scope

Original: A. J. Silberger, *The Langlands quotient theorem for p-adic groups*,
Math. Ann. 236 (1978), 95–104. Registered source
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
The full article was read in the parent task; the original page images for
pp.95 and 103 were reread while preparing this draft. No author-issued erratum
has been retained.

Page 95 defines a semistandard pair by its split component being a subtorus of
the fixed maximal split torus. Corollary 6.2 on p.103 compares a semistandard
regular-positive tempered datum with the previously fixed standard datum for
the same irreducible quotient class. It concludes that a Weyl representative
conjugates the pairs, Levis, tempered representations and parameters.

For split `GL_n`, the Weyl group is the permutation group and every Weyl class
has its permutation-matrix representative. Replacing a source representative
by the pure permutation representative changes it by an element of the
diagonal torus. That torus lies in the target Levi of a standard pair. This
replacement preserves the target pair and real character and changes the
transported representation only by an inner Levi equivalence. The conclusion
therefore permits the canonical permutation representative without narrowing
the source result. This representative replacement remains a proof obligation.

The source equality of real parameters is represented by equality of their
transported unramified positive characters. The map from real determinant
exponents to these characters is faithful: evaluation on an element with a
single uniformizer determinant recovers that coordinate from `q^(-tᵢ)`, since
`q > 1`. On the split component the positive block-size factors preserve this
faithfulness. This is the reason the character formulation retains the real
parameter assertion, not a claim that a separate faithfulness theorem has
already been implemented here.

The source names the unique quotient `J(σ,ν)`. Here an arbitrary actual
irreducible quotient is used, and two such quotients are related by an actual
representation equivalence. The regular-positive unique-quotient theorem
justifies this reformulation; uniqueness is not assumed as part of the datum.

The source proof chooses a Weyl representative standardizing the semistandard
pair, identifies the corresponding inductions and applies Proposition 6.1.
An eventual Lean proof must supply the semistandard standardization geometry,
the actual conjugate-induction transport, its compatibility with the normalized
real twists and temperedness, standard-data uniqueness, representative
replacement, and the coordinate/parameter conclusions. The conjugate-induction
construction alone proves none of the recovery conclusions. No proof of
Corollary 6.2 is supplied by this proposition definition.

## Construction dependency

The import `Langlands.Representation.Induction.ConjugateParabolic`, constructed
by Worker 264, provides the actual conjugate Levi embedding, its range subgroup
and normalized function-space induction used here. Its complete Lean/Markdown
pair was read and the exact statement compiled against that implementation.
The construction proves the standard-to-conjugate induction equivalence by
left translation and its intrinsic covariance, smoothness and naturality laws.
It does not provide the semistandard standardization geometry or the recovery
conclusions asserted here. Compilation and proposition inspection do not
establish semantic acceptance or a proof of this statement.
