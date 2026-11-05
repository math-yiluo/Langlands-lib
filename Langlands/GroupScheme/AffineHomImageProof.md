# Actual fppf image factorization for affine algebraic group homomorphisms

`Langlands.GroupScheme.affineHomImage` proves exactly
`Langlands.GroupScheme.AffineHomImageStatement.{u}` at an arbitrary universe
`u`. It applies to every field and every actual homomorphism between affine
group schemes locally of finite type over that field. It imposes no
smoothness, connectedness, reducedness or perfectness hypothesis.

The intermediate group is the existing actual schematic image
`AffineHomImage.image f`. The homomorphisms are its original
`AffineHomImage.projection f` and `AffineHomImage.inclusion f`. The existing
image construction makes the inclusion a closed subgroup inclusion, gives
the factorization, and makes the image affine and locally of finite type.
The target statement and all of its imported source pairs are unchanged.

The essential input is faithful flatness over Hopf subalgebras, supplied by
`HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem`.
The supporting port proves this theorem for finite-type commutative Hopf
algebras over every field, with independent universes for the field and
the Hopf algebra. A subalgebra is required to be stable under the antipode,
and its comultiplication must lie in the span of pure tensors of its
elements. No reducedness or characteristic restriction remains in its
conclusion.

The geometric adapter in `AffineHomImageHopfAdapter` obtains the actual
coordinate pullback using full faithfulness of `hopfSpec`. Scheme-theoretic
dominance of the image projection makes this pullback injective. Its
algebraic range satisfies the two Hopf-stability conditions: tensor-product
induction proves the comultiplication condition, and inverse naturality
for algebra cogroups proves antipode compatibility. Apply the ported
faithful-flatness theorem to that range and compose with its bijective
range restriction. The spectrum comparison then makes the actual
projection flat and scheme-surjective.

`AffineHomImageHopfReduction` completes the geometric argument. The
projection is locally of finite type because its composite with the image
structure morphism is the original source structure morphism. The image
is locally Noetherian, since it is locally of finite type over a field.
Consequently the projection is locally of finite presentation. Finally,
`AffineHomImage.kernel_range_projection` gives equality of the full actual
kernel ranges on every test scheme. These properties are exactly
`RelativeRoot.IsFppfQuotient` for the original kernel of `f`.

Surjectivity here is surjectivity of the underlying scheme map. The
conclusion does not assert surjectivity on the point group of each fixed
test scheme.

The theorem is the affine homomorphism theorem of J. S. Milne, *Algebraic
Groups*, corrected reprint (2022), Theorem 3.34, printed p. 75 (zero-based
PDF page 85), also Theorem 5.39, printed p. 108 (PDF page 118). The
registered source is `milne-2022-algebraic-groups`, SHA256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
The supporting algebraic route corresponds to Milne's Theorem 3.31,
printed pp. 73–74. The registered author errata snapshot
`milne-2022-algebraic-groups-errata-2026-11-04` has no correction to
Theorems 3.31 or 3.34. Its correction on printed p. 108 changes the second
`q` in Remark 5.40 to `q'`, without changing Theorem 5.39.

The algebraic source is the registered
`anthropic-flt-complete-lean-source-6e837e75`, commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, specifically
`Theorems/Thm_HopfAlgebra_faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem.lean`,
its matching `P2M/Sol/S_...` proof, and their supporting import closure.
The paired Markdown of each ported module records its original path,
fingerprint, mathematical proof route and compatibility changes.
Copyright and attribution are retained under `licenses/Anthropic-FLT/`.
The coordinate adapter and final geometric assembly are derived
arguments written for this target.
