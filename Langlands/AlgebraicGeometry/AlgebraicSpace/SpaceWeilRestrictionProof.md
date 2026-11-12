# Weil restriction of algebraic spaces along finite locally free maps

Author: Worker 110.

`Langlands.AlgebraicGeometry.AlgebraicSpace.spaceWeilRestriction` proves the exact
published proposition `SpaceWeilRestrictionStatement` from
[`SpaceWeilRestrictionStatement`](SpaceWeilRestrictionStatement.md).
This is Brian Conrad's Lemma 5.10, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed pp.17–18; registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

For arbitrary commutative rings `R` and `R'` in universe `u`, with `R'` a finite
projective `R`-algebra, let `X'` be a quasi-separated algebraic space of finite
type over `Spec R'`. The theorem supplies an algebraic-space structure on its
actual fppf Weil restriction, defined on every scheme test by pullback along
`Spec R' → Spec R`. The resulting space is quasi-separated and of finite type
over `Spec R`. It is separated if `X'` is separated, and of finite presentation
if `X'` is of finite presentation. There are no additional hypotheses.

The implemented proof applies the published theorem
`spaceWeilRestriction_of_geometricInputs` from
[`SpaceWeilRestrictionReduction`](SpaceWeilRestrictionReduction.md) to two
unconditional published proofs:

- `weilRestrictionDiagonal_proof`, from
  [`WeilRestrictionDiagonalProof`](WeilRestrictionDiagonalProof.md), gives the
  representable quasi-compact diagonal of the restricted full presheaf and its
  closedness when `X'` is separated.
- `weilRestrictionAffineEtaleAtlas`, from
  [`WeilRestrictionAffineEtaleAtlasProof`](WeilRestrictionAffineEtaleAtlasProof.md),
  gives étaleness and geometric surjectivity of the restricted affine atlas.

The reduction refines the supplied finite-type atlas to an actual affine one.
The affine Weil scheme represents its full restricted presheaf; composing that
comparison with the restricted atlas gives an étale surjective scheme atlas
of the restricted sheaf. Together with the first input's diagonal this constructs
the required algebraic-space witness. The same affine atlas proves finite type,
and the diagonal conclusions give quasi-separatedness and the conditional
separatedness. For finite presentation the reduction separately refines the
supplied finite-presentation atlas and uses preservation of finite presentation
by the affine Weil algebra.

Thus the final application discharges both geometric premises of the reduction;
neither is an assumption of this theorem. Their supporting modules explain the
full-test equalizer, local quasi-affine representation and gluing arguments.
This is a Library-derived assembly of those proofs of Conrad's assertion.
The universe parameter and the complete finite-projective ring-map scope are
retained. The separate rational-point topology statements of Proposition 5.11
are outside the theorem.
