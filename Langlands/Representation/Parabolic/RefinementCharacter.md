# The outer modulus on an actual Levi refinement

This is a derived construction and its intrinsic algebraic laws, used to
prepare normalized parabolic transitivity. It does not assert the transitivity
theorem.

Let `F` be a finite extension of `Q_p`, let `T` be compatible topological
data for `F`, let `B` be an ordered positive block shape of total rank `n`,
and let `S : Geometric.BlockRefinement B` refine each block. Write `M`
for `B.Levi F.Carrier`, `L` for the actual subgroup
`Geometric.refinedLevi F.Carrier B S`, and `V` for
`Geometric.refinedUnipotent F.Carrier B S`.
No positive total-rank assumption is needed for these intrinsic identities.

The published outer full character on `M` is

```text
delta_B(m) = product over i < j of
  |det(m_i)|_F^(B.size j) / |det(m_j)|_F^(B.size i).
```

Here the absolute value has the residue-cardinality normalization from
`Group.GL.NormalizedCharacter`, and the determinants are those of the
actual component matrices. This module proves that every component
determinant norm of an element of `V` is one. It follows that `V` lies in
`T.normOneLevi B`, and hence in the kernel of the full outer modulus.
The positive half used for induction and the inverse half used for Jacquet
normalization are both one on `V` as well.

The two new characters have domain the actual subgroup `L`:

- `T.refinedOuterModulus B S` is the restriction of `T.leviModulus B`.
- `T.refinedOuterHalfModulus B S` is the restriction of
  `T.leviHalfModulus B`, the canonical positive complex square root.

The implemented laws give their pointwise formulas, compatibility of
restriction with the positive and inverse halves, the square of the
positive half, continuity of the full character, and open kernels for
both full and positive-half characters. The inverse half has the same
kernel by the imported `Jacquet.inverseHalfCharacter_ker`.
The restricted characters are independent of the supplied compatible
topological data, as functions on the same algebraic groups.

## Provenance and implemented proofs

Bernstein--Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), Proposition 1.9(c), printed page 445 (PDF page 6), gives
composition of the normalized induction and Jacquet constructions.
Its proof explicitly calls for checking the normalizing factors.
Sections 2.1--2.3, printed page 446 (PDF page 7), describe the standard
Levi decompositions, ordered block specialization for `GL_n`, and
parabolic transitivity. These passages motivate this prerequisite;
the displayed componentwise character restriction is derived from the
published concrete definitions, not quoted as a separate source theorem.

Registered original: `bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

The proof of `determinantNorm_refinedUnipotent` applies the already
published
`GeneralLinear.BlockShape.determinant_eq_one_of_mem_unipotentSubgroup`
to the corresponding component of the actual product subgroup, then
applies the normalized absolute-value homomorphism to one. No determinant
lemma is duplicated. The kernel conclusions follow from the existing
`normOneLevi` and half-character laws. The new characters are compositions
with the subgroup inclusion, so their restriction identities are
definitional, continuity is composition with the continuous subtype map,
and open kernels are preimages of the published open kernels.

## Remaining obligations and scope

The inner refinement modulus is a separate character, constructed from
the refinements `S` in
[RefinementDefinitions](../Geometric/RefinementDefinitions.md).
The expected full character on the
composed smaller parabolic uses the product of that inner character and
`refinedOuterModulus`. This module constructs only the outer factor and
proves its triviality on the inner radical. It does not assume an inner
projection, supply a chosen equivalence of representation functors, or
state normalized transitivity. Identifying any explicit modulus formula
with Haar scaling remains a separate theorem obligation.
