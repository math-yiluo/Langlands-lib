# Conditional assembly for equal-rank trilinear uniqueness

This internal module specializes `EqualRankTrilinearReduction` to the actual row
Schwartz functions and coefficient models in the unchanged target. Its results
are conditional reductions. It does not prove the full JPSS uniqueness theorem.
All imports are published Library modules.

`invariantForms` is the full complex submodule of curried trilinear forms whose
simultaneous covariance is prescribed by a scalar function on the group. The
third action is an actual representation. `restrictInvariant` restricts these
forms to a stable test-function subspace and preserves their covariance. These
constructions impose no smoothness, finite-dimensionality, or nonzero-form
assumption.

`PointwiseInvariant` restates the pointwise translation premise in the published
target. `invariant_iff_pointwise` proves its equivalence with invariance for the
actual bundled row action, using equality of Schwartz functions from equality of
all their values.

`coefficientModel_uniqueness_of_source` uses `Whittaker.modelMap` and its
surjectivity to pull both forms back to their source representations. The
published surjective-pullback lemma then descends source uniqueness to the two
actual coefficient images. Neither injectivity nor a nonzero assumption on the
Whittaker functionals is used; models from zero functionals are covered.

`restriction_uniqueness_of_bilinear_equiv` assumes a linear equivalence between
the full invariant trilinear space on `rowVanishingAtZero` and the covariant
bilinear space on the two actual mirabolic restrictions. It also assumes the
latter space has scalar-module length at most one. It restricts two full forms,
transports them through the equivalence, applies the published bilinear
proportionality theorem, and transports the scalar-multiple equality back. The
nonzero assumption here concerns the restriction of the first form.

`source_uniqueness_of_mirabolic_bound` uses the supplied p-adic topology and
normalization and assumes three inputs: for each parameter a Frobenius linear
equivalence as above, one finite exceptional set outside which the mirabolic
bilinear length is at most one, and one finite exceptional set outside which all
residual GL bilinear forms vanish. The full trilinear covariance is
`determinantWeight abv g (-s)` and the mirabolic covariance is
`determinantWeight abv g (1 - s)`. The shift is retained exactly. The proof uses
evaluation at the zero row, its invariance under row translation, and the
published restriction-and-residual argument. The union of the two exceptional
sets is chosen before the parameter and before any forms.

`equalRankTrilinearUniqueness_of_source` packages source uniqueness as the exact
published `EqualRankTrilinearUniquenessStatement`, with independent field and
representation-carrier universes. The source-uniqueness hypothesis remains
explicit and unproved. Its exceptional set is chosen even before the two
Whittaker functionals, which suffices for the target's quantifier order.

The provenance is internal algebraic specialization of published definitions
and reduction lemmas. No Library statement or imported pair is edited. The
module neither constructs Frobenius reciprocity nor proves finite length,
irreducible mirabolic pairing rigidity, or central bilinear vanishing. Those
representation-theoretic inputs remain separate obligations for the parent task.
