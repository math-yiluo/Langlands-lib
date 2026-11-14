# Nonnegative restricted root depth gives lower neutral integrality

This internal supporting unit combines published sharp-fixer containment and
exact recovery of integral models. It does not assert existence of a fixer
model or prove the unconditional depth-zero opposite-factor statement.

Fix a nonarchimedean local field `F`, its actual inertia fixed field `K`,
and an affine group scheme `G` over `F`. Let `L` and `E` be actual relative
component model data for `G` over the integers of `F` and for `G_K` over the
integers of `K`. An `UnramifiedComponentModelRecovery L E` identifies both
the full and neutral models after unramified base change, compatibly with
their generic fibres and inclusions.

`mem_neutral_integralPoints_of_extend_mem_sharpFixer` takes upper building
data `B` and an arbitrary apartment subset `Ω`. Assume that the full upper
model has integral-point image equal to the intersection of the character
valuation kernel with the pointwise fixer of `B.apartmentMap '' Ω`. Then
every `g ∈ G(F)` whose extension belongs to `B.sharpFixer Ω` lies in
`L.neutral.integralPoints`. The published
`unramifiedSharpFixer_le_neutral` puts its extension in the upper neutral
model, and `neutral_integralPoints_eq_comap` descends that membership.
No equality between neutral integral points and a fixer is an input.

For the root-specific construction, also assume that `G` is smooth.
Supply a split torus `S` embedded in `G`, a commutative group scheme `T`
with an embedding `iT_K` that is a maximal split torus of connected
reductive `G_K`, a factorization `S → T → G` of the embedding of `S`,
opposite factor pairs for `iT_K`, an upper KP apartment datum `D`, a
centralizer datum `C`, and V6 compatibility for the actual unramified
integer valuation. Fix an apartment point `x` and require the preceding
full upper fixer equality for the singleton `{x}`.

`mem_neutral_integralPoints_of_nonnegative_restrictedDepth` proves that
any point `g` of an actual lower root subgroup whose torus-then-field
restricted root value at `x` is nonnegative lies in the lower neutral
model's integral-point image. The published
`rationalExtend_mem_sharpFixer_of_nonneg` gives upper sharp-fixer
membership. The supplied upper data are packaged into the existing
`MaximalUnramified.BuildingData` structure, and the preceding descent
lemma finishes the argument.

`neutralSectionOfNonnegativeRestrictedDepth` chooses an actual integral
section of this lower neutral model. Its `_generic` theorem proves that
the generic point of this section is the original `g`. This is a section
of the supplied model, rather than an abstract integrality certificate.
The construction works at arbitrary universe `u`; it does not require
`S` to be maximal, a lower KP apartment, Galois fixedness of `x`, a
neutral fixer-image equality, or a zero datum.

The provenance is the internal composition of the three published
lemmas named above. The converse from lower root integrality to
nonnegative restricted depth, radical nonvanishing at value zero, and
existence of all required models remain separate obligations.
