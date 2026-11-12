# The origin-component direction of the field Picard-zero comparison

This module proves the "connected component of the origin implies Picard-zero"
half of `Langlands.AbelianScheme.FieldPicardZeroGeometricComponentComparisonStatement`.
It imports the published proof
`Langlands.AbelianScheme.fieldPicardZeroComponentConstancy` from
`Langlands.AlgebraicGeometry.Picard.FieldPicardZeroComponentConstancyProof`.
The main theorem therefore has only the original universal-family hypotheses;
component constancy is not an additional hypothesis.
`FieldPicardZeroComponentForward` supplies the opposite implication, and
`FieldPicardZeroGeometricComponentComparisonProof` assembles the exact comparison.

## Declarations

- `RigidifiedLineBundle.classifyFamily_self`: a universal family `L` over `P` is
  classified by `𝟙 P`. The proof applies injectivity of the classifying map of
  the universal property at `P`, then `classifyFamily_spec` and
  `classifyingMap_id`.
- `isPicardZeroFamily_pullback_of_eq_trivialParameter`: if a parameter map
  `h : T ⟶ P` equals `Over.mkIdTerminal.from T ≫ trivialParameter`, then the
  pulled-back family is geometrically Picard-zero. By `classifyFamily_pullback`,
  `classifyFamily_self` and `classifyFamily_trivial`, the pulled-back family and
  the relative trivial family over `T` have the same classifying map, so
  `isoOfClassifyFamilyEq` gives an isomorphism between them.
  `isPicardZeroFamily_iff_of_iso` and `isPicardZeroFamily_trivial` finish.
- `trivialParameter_apply`: every point of `Spec k` maps under the trivial
  parameter to `fullPicardOriginPoint k A L hL`. That point is defined as the
  image of the closed point, and `Spec k` is a subsingleton.
- `isPicardZeroFamily_of_mem_originComponent`: the main theorem. It uses the
  published constancy theorem and assumes `LocallyOfFiniteType P.hom`, an algebraically closed
  field `K` and a geometric point `s : Spec K ⟶ P.left` whose range lies in the
  connected component of the origin point. It concludes that the family pulled
  back along `Over.homMk s rfl` is geometrically Picard-zero.

## Proof of the main theorem

The comparison point is `s₀ = ι ≫ tp.left`. Here `ι` is the spectrum map
`Spec (AlgebraicClosure k) ⟶ Spec k` of the algebra map, and `tp` is the
trivial parameter of the universal family. The published constancy theorem is applied
with `x = fullPicardOriginPoint k A L hL`, the geometric points `s₀` and `s`,
and the hypotheses `hP` and `hL`. It needs three inputs:

- the range of `s₀` lies in the connected component of the origin, because
  every point of the range is `tp.left (ι y)`, which equals the origin by
  `trivialParameter_apply`;
- the range of `s` lies in that component, which is the hypothesis;
- the family pulled back along `s₀` is Picard-zero. This follows from
  `isPicardZeroFamily_pullback_of_eq_trivialParameter`, because
  `Over.homMk s₀ rfl` is the composite of the terminal map with `tp` (checked
  by `Over` extensionality and `simp`).

## Provenance

This is internal plumbing. The mathematical input is the published proof of
the constancy statement, a derived strengthening of Lemma (7.15) of Edixhoven, van der Geer and Moonen,
*Abelian Varieties* (source ID
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, printed p. 104,
PDF p. 108). That Lemma says that for a line bundle on `X_T` over a connected
`k`-scheme `T`, the homomorphism `ϕ_{L_t}` does not depend on the `k`-point `t`.
The constancy statement's Markdown explains how it differs from the Lemma.


## Authorship and dependency boundary

This pair adapts the carried Task 2104 draft (historically Worker 860) to the
current Library. Worker 2104 replaced its explicit constancy assumption with
the published theorem; the classifying maps, trivial parameter and origin are
the existing Library constructions. No new comparison predicate is introduced.
The imported constancy proof uses the universal group object and the Mumford
classifier; this assembly adds no field-extension comparison premise.

The argument imports the constancy proof and uses the existing full Picard
origin and Mathlib connected component. It assumes no Picard-zero open locus
and uses neither geometric-point nor all-test-scheme openness.
