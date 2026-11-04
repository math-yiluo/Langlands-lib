# Reduction of the corrected chamber normalizer-coset lemma

This derived internal unit develops the actual-subgroup argument for the replacement of
Kaletha–Prasad Lemma 5.3.5 in the authors' 1 November 2024 corrections, PDF page 30.
It does not yet prove the exact global target. Chamber product surjectivity is
an explicit input to the local reduction; its unconditional proof is separately
owned by the chamber-product task.

The proposition `UnipotentNormalizerCosetReductionStatement` quantifies over
the same arbitrary-universe local fields, affine group schemes and actual data
`P`. It assumes normality of the actual `P.normalizerZero`, the existing
`P.ChamberIwahoriDecompositionStatement`, and the retained apartment axioms.
For every chamber and generic cocharacter it concludes the existing
`P.UnipotentNormalizerCoset C ν`, using the literal standard unipotent and the
orientation `n' n⁻¹`. The theorem `unipotentNormalizerCosetReduction` proves
this conditional statement. Neither intermediate input is asserted to hold
unconditionally by this unit.

The literal `standardUnipotentPoints P.i ν ∅` is contained in the dynamic
unipotent for `ν`, since `ν` itself is a standard cocharacter for the empty
index. This inclusion requires neither genericity nor an equality between
standard and dynamic subgroup functors.

Suppose `u n ∈ P_C`, with `u ∈ U(ν)` and `n ∈ N(F)`. A factorization in the
reverse chamber order writes `u n = a z b`, with `a ∈ U(ν)`, `z ∈ Z(F)^0`,
and `b ∈ U(-ν)`. Then
`n z⁻¹ = (u⁻¹ a)(z b z⁻¹)`. The second factor belongs to `U(-ν)` because
the whole torus centralizer centralizes the cocharacter and thus normalizes
its dynamic unipotent. The first factor belongs to `U(ν)`.

The published `normalizer_eq_one_of_unipotent_product` applied to `-ν`
makes this normalizing product the identity. Its opposite-cocharacter
convention is matched by `groupHom_neg_comp_eq_oppositeCocharacter`.
Consequently `n = z ∈ Z(F)^0`. This uses all-test opposite-cell injectivity,
already proved for an affine ambient group; it adds no rational Bruhat premise.

This reduction has internal provenance: it combines the corrected lemma's
reverse Iwahori factorization argument with the Library's proved
opposite-unipotent normalizer separation. No chamber product theorem is
claimed as proved here.

The proof imports `IwahoriWeylChamberLemmas` and uses its
`P.normalizer_smul_isChamber` to transport chambers by the actual normalizer.
That theorem follows from affine-root preservation under the retained apartment
axioms. Assuming normality of the actual
`normalizerZero`, its conjugation stability combines with the published
sharp-fixer covariance to prove full-parahoric covariance.

For the forward coset implication, `n = u n' p` gives
`u (n' n⁻¹) = n p⁻¹ n⁻¹ ∈ P_(nC)`. Apply the local intersection argument in the
translated chamber. This yields exactly `n' n⁻¹ ∈ normalizerZero`.
For the reverse implication, normality first rotates the two factors and then
inversion gives `n'⁻¹ n ∈ normalizerZero`. Its image is in every parahoric, so
choose the unipotent factor to be the identity and the parahoric factor to be
`n'⁻¹ n`.

The assembled reduction retains both currently missing inputs explicitly:
actual zero-subgroup normality and reverse chamber product surjectivity.
It is not the unconditional `UnipotentNormalizerCosetStatement`.

The final adapters extract precisely the needed range clause from the existing
`ChamberIwahoriDecompositionStatement`. Negating a generic cocharacter preserves
genericity by linearity of the lattice pairing. Every chamber has a point,
namely the facet representative in its definition. Applying the chamber statement
at that point and `-ν` gives the reverse product used above.

The global assembly takes the chamber statement for every actual datum
and `IwahoriWeylExactSequenceStatement`, extracting only zero-subgroup normality
from the latter. It then proves the exact `UnipotentNormalizerCosetStatement`
with all its original field, apartment and genericity hypotheses. These two
inputs are still explicit intermediate obligations, so this assembly is not an
unconditional proof of the task's published target.
