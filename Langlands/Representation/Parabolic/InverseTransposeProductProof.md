# Inverse transpose of normalized block products

Author: Worker 163.

`Langlands.Parabolic.inverseTransposeProduct.{uF,uV}` proves the unchanged
published proposition `Langlands.Parabolic.InverseTransposeProductStatement`.
It combines the actual product equivalence, determinant-twist equality, and
finite-sequence order clause. Its field and carrier universes are independent.
The proof imports the existing statement and transport constructions without
modifying them.

## Actual product equivalence

Write `θ_r = GeneralLinear.inverseTranspose r F.Carrier`,
`w = B.reverseMatrix F.Carrier`, and
`P = PiTensorProduct.reindex ℂ V Fin.revPerm`. The theorem
`normalizedProductInverseTranspose` proves the published product clause for
every positive rank, every actual block shape, and arbitrary smooth complex
block representations on the dependent modules `V i`. It composes two published
transport results on their actual smooth covariant-function carriers.

First, `T.inverseTransposeProductToOppositeEquiv B σ` sends the inverse-transpose
pullback of upper normalized induction to opposite normalized induction of the
blockwise pullbacks `τ_i = (σ_i).comp θ_(B.size i).toMonoidHom`. Its forward and
inverse maps both precompose with `θ_n`. In the imported
`Representation.Induction.InverseTranspose` module, the actual diagonal-block
identity `leviProjection_oppositeToUpperInverseTranspose` and the character
identity `parabolicHalfModulus_oppositeToUpperInverseTranspose` prove covariance.
The latter uses inversion of the explicit determinant-product modulus and the
inverse law of the canonical positive square-root homomorphism. Tensor-action
compatibility holds on the whole `PiTensorProduct` carrier. Thus neither an
inducing-action identity nor a normalization identity is assumed here.

Second, the private `inverseTransposeOppositeReversal` helper applies
`Langlands.glOppositeProductReversal` to the family `τ`. Its smoothness
hypotheses follow from `Langlands.isSmooth_comp` and
`GeneralLinear.continuous_inverseTranspose` for each block. The published
reversal equivalence has forward map `h ↦ (x ↦ P(h(w*x)))` and inverse map
`k ↦ (x ↦ P.symm(k(w⁻¹*x)))`. It uses the actual reversed block family
`V i.rev`, the diagonal-projection comparison under conjugation by `w`, and
the opposite-to-reversed-upper positive half-modulus identity. Its tensor
permutation is the actual dependent reindexing equivalence.

The helper retains this equivalence in `Nonempty`; the product proof extracts
it and composes it with the first transport using `Representation.Equiv.trans`.
Consequently the witness it supplies has the formulas

```text
E(f)(x)       = P(f(θ_n(w*x))),
E.symm(k)(x)  = P.symm(k(w⁻¹*θ_n(x))).
```

These describe the chosen composition of the imported maps; the conclusion of
the product clause requires only existence of the equivariant linear
equivalence. No additional formula theorem is asserted in this module. The
inverse formula uses `w⁻¹`, and the proof never assumes that `w` is involutive.
Pointwise linearity, both inverse identities and right-translation equivariance
are bundled in the imported equivalences and preserved by their composition.

The carriers require a single open subgroup fixing the entire function under
right translation. The first transport takes an original uniform open
stabilizer `K` to its continuous comap under `θ_n`: for every `x` and every
`k` in this comap, `f(θ_n(x*k)) = f(θ_n(x)*θ_n(k)) = f(θ_n(x))`.
The reversal transport preserves that same subgroup, since left translation
by `w` and postcomposition by `P` preserve right invariance. Its inverse also
preserves the chosen subgroup, and inverse precomposition again uses the
continuous comap. This supplies uniform open stabilizers in both directions,
not merely local constancy at individual points.

The private helper works for all natural ranks, including the empty block
family. The public product theorem retains the positive-rank quantifier in the
specified statement, although its proof does not use positivity. It adds no
irreducibility, admissibility, finite-length, temperedness or classification
hypothesis, and includes reducible and zero block representations.

## Determinant twists and exponent order

`determinantPowerCharacter_inverseTranspose` uses the published
`T.determinantNorm_inverseTranspose`: the determinant of inverse transpose is
the inverse determinant, and the normalized absolute value is multiplicative.
The real-power character preserves inversion, and `realPowerCharacter_neg`
identifies the inverse character with the negative exponent. Applying
`twist_comp` then proves `inverseTransposeDeterminantTwist`, an equality of
actual representations on the same carrier. This clause holds for every
natural rank and every complex representation, without a smoothness hypothesis.

`reverseNegateStrictAnti` proves the finite-order clause. For `i < j`,
`Fin.rev_lt_rev` gives `j.rev < i.rev`. Strict antitonicity of `u` gives
`u i.rev < u j.rev`, and `neg_lt_neg` gives `-u j.rev < -u i.rev`, the required
strict decrease of the reversed, negated sequence. The proof treats empty and
singleton sequences by the same universal argument.

The final theorem conjoins these three clauses for every prime, p-adic field
and compatible `TopologicalData`. `inverseTransposeProductLift` specializes the
same theorem to carrier universe `max uV uL`, proving the published
`InverseTransposeProductLiftStatement` with three independent universes. It
asserts no additional equivalence between lifted and unlifted induction.

## Provenance

This is an internal assembly from the published actual induction, block
geometry, tensor reindexing, character, smooth pullback and twist constructions.
The transport modules are `Representation.Induction.InverseTranspose` and
`Representation.Induction.OppositeProductReversalProof`; smoothness and twist
compatibility use `Representation.Smooth.Transfer.PullbackProof` and
`Representation.Twist.PullbackProof`. The order step uses Mathlib's finite-index
reversal and ordered negation. No external theorem or original-literature
identification is claimed. In particular this theorem does not identify an
induced representation with its smooth contragredient or prove any analytic
preservation property.
