# The scalar cone of an actual induction embedding

`Langlands.squareIntegrableInductionEmbeddingCone` proves exactly
[`Langlands.SquareIntegrableInductionEmbeddingConeStatement`](SquareIntegrableInductionEmbeddingConeStatement.md).
Worker 320 supplied the proof draft; Worker 544 checked its interfaces,
dependency independence and complete quantified target, and prepared these
paired modules for publication.

An injective intertwiner from the explicitly nontrivial source is nonzero.
The complex-linear equivalence
`Parabolic.FirstAdjointness.equiv` in
[`NaturalFirstAdjointness`](../Parabolic/NaturalFirstAdjointness.md) therefore
gives a nonzero map from the whole normalized upper Jacquet module into the
actual inducing Levi representation. The proof takes `SmoothRep.image` of
this map and corestricts it to its invariant image. The corestriction is
surjective. If the image were subsingleton, every value of the adjunction map
would vanish, contradicting its nonzeroness. Thus this actual smooth image is
nontrivial and is a quotient of the whole Jacquet module.

`SmoothRep.IsQuotient.isSubquotient` in
[`SupercuspidalSupport`](../Classification/SupercuspidalSupport.md) converts
this actual quotient into the existing subquotient relation. Only this
algebraic conversion is used from that module. Equality of underlying vectors
restricts the supplied split-centre scalar equation from the inducing
representation to its image. Applying the published
[`Langlands.squareIntegrableActualJacquetCone`](SquareIntegrableActualJacquetConeProof.md)
to this image, the same character and the same supplied real-part vector proves
zero total sum and strictly positive proper initial sums.

The field and carrier universes remain independent. The target uses carriers
in `Type (max uF uV)`; the last application specializes the scalar Jacquet-cone
theorem to field universe `uF` and carrier universe `max uF uV`. This retains the
actual induction, quotient and image carriers. No irreducibility or finite-length
hypothesis is introduced. The upper induction uses positive half-modulus
covariance and right translation, and its matching upper Jacquet module uses
the inverse half-modulus.

The provenance is the internal composition of these published algebraic and
analytic results. A recursive source audit of both new modules and their 426
project modules found no missing imports and no occurrence of the excluded
segment-classification, ordered-head, quotient-coverage, tempered-block
uniqueness, square-integrable-exhaustion or regular-exhaustion declarations or
their proof names. Every existing Lean/Markdown import pair agrees with the
Library base. The scalar Jacquet-cone input uses local central-scalar detection,
Jacquet admissibility, scalar compatibility and the analytic strict exponent
criterion. This proof constructs no segment head and supplies neither factor
commutation nor analytic classification.
