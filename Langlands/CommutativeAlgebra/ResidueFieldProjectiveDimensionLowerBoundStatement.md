# A lower bound for the projective dimension of the residue field

`Langlands.CommutativeAlgebra.ResidueFieldProjectiveDimensionLowerBoundStatement.{u}`
asserts that for every Noetherian local commutative ring `R : Type u`,

```lean
((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤
  CategoryTheory.projectiveDimension
    (ModuleCat.of R (IsLocalRing.ResidueField R))
```

The natural number on the left is the minimum number of generators of the
maximal ideal. In a Noetherian local ring this equals the dimension of the
cotangent space over the residue field, by Mathlib's
`IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`. Thus this
is the usual embedding dimension. The right side is Mathlib's categorical
projective dimension, defined by Ext vanishing, for the canonical residue-field
module. Both sides are compared in `WithBot ℕ∞`.

There is no finite-projective-dimension hypothesis: an infinite projective
dimension also satisfies the inequality. No domain or characteristic
hypothesis is imposed, and the universe `u` is arbitrary. The Lean file
defines a proposition; it supplies no proof.

## Original source and role

This is Stacks Project Lemma 10.110.3,
[Tag 00OA](https://stacks.math.columbia.edu/tag/00OA), translated using the
equality between the minimal number of generators and cotangent-space
dimension. The complete original page and all ten comments are retained in
`00OA.html` of registered source
`stacks-residue-field-projective-dimension-bounds-2026-11-01`, directory
SHA-256 `40635b9a819b6011c03de10b01cecd53bb1c9e67a82d3022bfa106470bac0743`.
The complete page and its comments have been read. There is no separate
project errata note for this source. The comments record corrections to the
Koszul differential sign and the comparison-map reference; this statement
contains neither a differential nor a claimed implemented proof.

Together with the upper bound on finite residue-field projective dimension
in Tag 00OB, this inequality is used for implication (1) to (3) of
Proposition 10.110.5, Tag 00OC. It does not assume the regularity criterion,
regularity of localizations, or finite projective dimension of all finite
modules.
