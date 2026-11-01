# Complete gamma products for large second twists

This is an internal composition of the actual adjacent-rank whole-image theorem
and the arbitrary-test gamma comparison. It supplies the complete certified
gamma product on the normalized lower induction for all sufficiently large real
second twists. Continuation to the original character remains separate.

`AdjacentRankLargeTwistGamma` fixes the original full-type first block `σ`, the
original test `τ`, the additive character and scalar Haar measure, and the base
quasicharacter `χ₀`. It asserts one real bound before the real twist `u`. Above
that bound, let `χ = χ₀ |.|^u` in the existing spectral normalization, and form
the actual normalized opposite-parabolic induction of the ordered blocks
`(σ, rankOneExtensionCharacter χ)`. There are rational functions `G₀` and `G₁`
with complete symmetric gamma certificates for `(τ, σ)` and
`(τ, rankOneExtensionCharacter χ)`, and their product has a complete certificate
for `(τ, induced representation)`. The original block and test carriers have
independent universes. Neither is required to be irreducible.

`adjacentRankLargeTwistGamma` proves this predicate under full Whittaker type of
both original representations and self-duality of the supplied scalar Haar
measure. It chooses nonzero standard and inverse-character functionals, installs
the actual invariant unipotent Haar measure, and uses the constructed compatible
quotient measure. The bound is the published whole-image bound associated with
the block functional and base character. Above it, the whole-image theorem gives
one actual nonzero induced functional and equality of the entire model-map
range with its coefficient range. The normalized lower induction has full
Whittaker type by complete ordered-family reversal. These data satisfy the
arbitrary-test image gamma theorem.

The helper `isPadicSymmetricGammaFactor_comm` preserves the entire gamma
certificate when exchanging full-type representations. Unequal ranks use the
existing convention of putting the larger rank first. Equal ranks use the
published equal-rank gamma exchange theorem at the same character and measure.
This helper puts the block and induced certificates in the required test-first
order. The scalar character is transported to the lifted character by the actual
`ULift` representation equivalence, preserving every certificate clause.

No unrestricted or finite-block JPSS multiplicativity theorem is used. This
result proves the large-twist assertion only; it does not assert continuation
to zero, the arbitrary upper-family closed base, or completion of its parent task.
