# Nonzero Jacquet modules along a uniform shape

Helper module for the proof of `JuxtaposedSegmentSocleReverseProductStructure`
(Zelevinsky 1980, Proposition 4.6, juxtaposed case). It supplies the positivity
hypothesis of `JuxtaposedShuffle.jacquetImage_strictMono`
(`JuxtaposedJacquetImage`): a nonzero step quotient has a nonzero Jacquet module.

## Declarations

- `eq_uniform_of_levisAssociated`: if the standard Levi of a block shape `C` of
  `m * r` is associated (conjugate by a permutation matrix) to the uniform Levi
  `GL_r^m` of `BlockShape.uniform m r hr`, then `C` equals the uniform shape.
  Proof: the conjugating permutation induces a bijection `blockMap` of blocks
  with equal sizes (`TotalConjugatingCount.length_eq`, `blockMap_surjective`,
  `size_blockMap`), so every block of `C` has size `r` and there are `m` blocks;
  `TotalConjugatingCount.shape_ext` concludes.
- `nontrivial_jacquet_of_isSubquotient`: for quasicuspidal smooth `σ` on the
  uniform Levi, every nonzero smooth subquotient `Q` of the normalized induction
  `i_C(σ)` along the uniform shape `C` has a nonzero normalized Jacquet module
  along `C`. Proof: minimal nonzero Jacquet descent gives a shape `C'` with
  `J_{C'}(Q)` nonzero and quasicuspidal. If `C'` is associated to `C`, then
  `C' = C` by the previous lemma. Otherwise `J_{C'}(Q)` is a quasicuspidal
  subquotient of `J_{C'}(i_C σ)` (`normalizedJacquetSubquotient`), hence zero by
  the nonassociated vanishing theorem, a contradiction. This repeats the proof of
  the Library theorem `JacquetLength.one_le_jacquetLength_of_isSubquotient`,
  with the single shape `C` in place of a summed length.
- `nontrivial_jacquet_stepQuotient`: if a representation `π` (carrier in
  `Type (max uF uV)`) has an injective intertwiner into `i_C(σ)`, then for
  subrepresentations `X ≤ Y` of `π` with `Y/X` nonzero, the Jacquet module of
  `stepQuotient X Y` along `C` is nonzero. Proof: `π`, `Y` and `Y/X` are smooth,
  and `Y/X` is a subquotient of `i_C(σ)` through `Y ↪ π ↪ i_C(σ)` and
  `Y ↠ Y/X`; apply the previous lemma.

## Hypotheses

`MinimalNonzeroJacquetTheorem` (BZ77 2.14(1), proved in the Library as
`CuspidalSupport.minimalNonzeroJacquet`) and
`NonassociatedJacquetSubquotientsTheorem` (BZ77 2.13(b), proved in the Library as
`CuspidalSupport.nonassociatedJacquetSubquotients`, task
b17b8c8c-858b-4b48-994b-e3641cb05f02) enter as hypotheses. The final proof
`JuxtaposedSegmentSocleReverseProductStructureProof` discharges both with these
published theorems.

## Provenance

Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), 2.13 and 2.14. The statements here are derived specializations to the
uniform shape with no single printed counterpart.
