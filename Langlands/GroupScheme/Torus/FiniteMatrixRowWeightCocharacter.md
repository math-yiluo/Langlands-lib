# Restricting matrix row weights to a cocharacter

This internal derived unit restricts the inverse-right row weights of a split
torus to a cocharacter. Let `K` be any field, `D` a division `K`-algebra, `n` a
finite row index, and `b` a finite `K`-basis of `Matrix n n D`. Let
`i : 𝔾ₘ^I ⟶ groupScheme b` be any group-scheme morphism with `I` finite. Neither
faithfulness, infinitude of `K`, nor a restriction on characteristic is assumed.

For a cocharacter `ν` of the standard split torus and an integer `c`,
`cocharacterWeightSupport i ν c` is the finite regular weight support filtered by
`⟨χ_m, ν⟩ = c`, where `χ_m` is the actual character corresponding to the exponent
`m : I → ℤ`. `mem_cocharacterWeightSupport` gives precisely this membership
condition. The regular support and the spaces `rowWeightSpace i m` use the
inverse-right convention of `FiniteMatrixRowWeights`.

`Lie.characterValue_cocharacter` proves that an actual character `χ`, evaluated
at the image of a coefficient-algebra point `t` under `ν`, is the coefficient
unit of `t` raised to `⟨χ, ν⟩`. This follows by writing the endomorphism `ν ≫ χ`
of the multiplicative group as its integer multiple of the identity and applying
the published power-map identity. `splitTorus.exponentValue_cocharacter` gives
the same result in exponent coordinates.

`rowActionOver_cocharacter_eq_sum` substitutes this formula into the finite
expansion of the row action by its projections.
`rowActionOver_cocharacter_of_mem` shows that a vector in `rowWeightSpace i m`
satisfies the integer eigenvector equation of weight `⟨χ_m, ν⟩` on every
commutative coefficient algebra.

Conversely, `sum_rowWeightProjection_of_cocharacter` assumes that a constant row
`v : n → D` satisfies the weight-`c` equation on every commutative coefficient
algebra. It proves the reconstruction formula
`∑ m ∈ cocharacterWeightSupport i ν c, rowWeightProjection i m v = v`.
The proof evaluates that equation in the Laurent polynomial algebra at the point
corresponding to its coordinate unit. Each character becomes the Laurent monomial
of degree `⟨χ_m, ν⟩`. Applying the actual coefficient functional of degree `c`
entrywise retains exactly the displayed terms. This argument works over finite
fields and in characteristic 2.

`mem_iSup_rowWeightSpace_of_cocharacter` then places `v` in the supremum of those
matching row spaces, since each projected vector belongs to its corresponding
space. All assertions concern the actual all-test row action and the finite
universal idempotent support. They impose no isometry or maximality hypotheses
and do not yet assert the maximal-isometry-torus multiplicity theorem.

The provenance is internal: the proof combines the published character lattice
and power-map identities, the previously constructed row action, and coefficient
extraction in a Laurent polynomial algebra.

The character-evaluation helper has the same mathematical identity as
`CoordinateWeights.characterValue_cocharacter` in
[GenericTorusCocharacter](../Rational/GenericTorusCocharacter.md), but retains
a bundled coefficient algebra and `Gm.affineUnitsEquiv` in its statement.
Both interfaces are retained because substituting one changes the statement's
coefficient presentation.
