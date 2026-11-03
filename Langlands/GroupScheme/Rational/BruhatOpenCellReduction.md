# Rational Bruhat contraction inputs from the opposite open cell

This internal unit derives the geometric contraction inputs of
`Rational.BruhatContractionReduction` from the explicit proposition
`OppositeCellStatement`. The ambient group is smooth and affine over an
arbitrary field in universe `u`.

`Dynamic.oppositeCellOrbitLift` treats two cocharacters `a ≫ i` and
`b ≫ i` factoring through the same commutative group scheme. Given an
actual orbit extension for the first cocharacter with value the identity
at zero, it constructs a morphism through the canonical
`U(-(b ≫ i)) × P(b ≫ i)` on the whole affine line.
The construction uses the canonical affine representatives from
`Dynamic.AffineRepresentability`. The supplied opposite-cell statement
makes their multiplication an open immersion. The common commutative
group gives normalization of both represented ranges under `a ≫ i`.
The normalized-open-product lift then constructs the actual lift.
`Dynamic.oppositeCellOrbitLift_fac` proves that composing it with
multiplication recovers the supplied extension. The represented-lift
adapter gives `Dynamic.hasProductContraction_of_oppositeCell`: every
rational point contracting to the identity under the first cocharacter
has the required whole-affine-line contraction through the opposite cell.
Affineness supplies the separatedness needed by the lift.

For an actual normalizing point `n`, the chosen automorphism
`normalizingAut i n` transports `ν` to a cocharacter `ξ` of the same
commutative group. The published equation `groupHom_cocharacterAut_comp`
identifies its image with `Int(n)χ`, where `χ` is the image of `ν`.
Applying the preceding construction gives exactly
`HasNormalizerProductContractions i ν`. No genericity premise for the
transported cocharacter is used.

The same canonical representatives and the supplied open immersion give
all-test multiplication injectivity via the existing open-immersion
adapter. Together these results feed the published contraction reduction.
The resulting Weyl factorization retains the identity between `Z(χ)`
and the whole-group centralizer of the commutative source. The final
`hasRationalBruhatDecomposition_of_oppositeCell` also retains the covering
`G(k) = U(χ)(k) N(k) U(χ)(k)`. Its conclusion is the existing
`HasRationalBruhatDecomposition`, with the actual dynamic parabolic double
cosets and quotient of normalizer points by centralizer points.

The provenance is an internal composition of the named imported
constructions, rather than a new claim from external literature.
`OppositeCellStatement` is an explicit assumption, not a theorem proved
here. The covering and centralizer identity remain separate proof
obligations. This unit does not prove the unchanged full
`RationalBruhatStatement`, generic minimality, or existence of the
opposite open cell. No splitness, perfectness, characteristic, field-size
or reductivity premise is added.
