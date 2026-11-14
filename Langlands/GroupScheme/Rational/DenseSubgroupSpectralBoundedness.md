# Spectral boundedness of dense rational subgroup families over local fields

This derived internal module extends the published whole-group local-field
spectral criterion to an arbitrary specified dense subgroup family. It is an
auxiliary result for the bounded-open-normalizer problem.

`DenseSubgroupSpectralBoundednessStatement.{u,v}` concerns a connected
reductive group `G` over a nonarchimedean local field `F : Type u`, an
arbitrary group `I : Type v`, and a monoid homomorphism `α : I →* G(F)`.
Its hypotheses are density of the union of images of these actual rational
sections, a closed faithful matrix representation `ρ` of `G`, and integrality
of every characteristic coefficient of `ρ(α i)`. It concludes
`IsAlgebraicallyBounded F G.X (Set.range α)`. The family need not be
surjective. Integrality and boundedness concern its image.

The theorem `denseSubgroupSpectralBoundedness` proves this proposition. Equip
the algebraic closure `K` of `F` with the published extended valuation. The
family extends by the actual monoid homomorphism `baseChangeSectionHom`;
its values are the actual `geometricRationalPoint` extensions. The
representation extends to a closed faithful representation over `K`.
Characteristic-coefficient integrality is preserved by the published
base-change comparison. The published
`MatrixRepresentation.isAlgebraicallyBounded_range_of_dense` gives
boundedness of the extended image, using the trivial geometric unipotent
radical from connected reductivity. Cofinality of the algebraic extension's
valuation then descends boundedness to the original image. The set identity
used in this descent is exactly the image of `Set.range α` under extension
of rational sections.

The auxiliary theorem
`hasDenseRationalPointFamily_geometricRationalPoint` works over any field
extension `k → K` with the fields in the same universe, for an arbitrary
index type in a possibly different universe. The scalar-extension projection
is open, so the preimage of the original dense union is dense. The published
`range_geometricRationalPoint` identifies that preimage with the union of
images of the extended sections.

The module uses published geometric and spectral proofs throughout. Its
statement is a derived family generalization; no external result or unproved
Library statement is an additional premise. It does not establish
characteristic-coefficient integrality for a normalizer, and therefore does
not by itself prove boundedness of open-subgroup normalizers.
