# Dynamic presentations after a trivial split-radical reduction

Author: Worker 1478.

This internal adapter constructs actual dynamic-parabolic presentation data for
a supplied pseudo-parabolic inclusion, conditional on an exact replacement
of its ordinary-radical product and triviality of the replacement factor.
It does not prove that product replacement or the unrestricted rational-lifting
statement. All declarations work over every field `k : Type u`, at arbitrary
universe `u`, with no characteristic, perfectness or field-size restriction.

`DynamicParabolicPresentation i` records an actual cocharacter of the original
ambient group and a proof that the original supplied inclusion `i : P → G`
represents its dynamic parabolic on every relative scheme test. In particular,
its source remains the original group scheme `P`. The representation proof
contains monicity and exact equality of subgroup functors.

`DynamicParabolicPresentation.ofSplitProduct` takes the original
`IsPseudoParabolicSubgroup i`, a supplied homomorphism `n : N → G` whose
full subgroup-functor range is bottom, and an explicit all-test product
replacement. For every represented ordinary ground-field radical `j` and every
cocharacter, this input identifies the existing fppf-local product of the
dynamic parabolic with `range j` with its product with `range n`. Its intended
application uses a represented split ground-field radical for `n`; the adapter
only needs its trivial range and the displayed product equality. It does not
require or prove any radical property of `n`.

The constructor extracts the ordinary radical and cocharacter from the original
pseudo-parabolic presentation. The supplied equivalence turns that presentation
into an fppf-local product with `range n`. The published affine dynamic
representability theorem supplies a monomorphic representative of the left
factor. Its fppf saturation makes the product with the trivial right factor
equal to that factor on all tests. Closedness of the original pseudo-parabolic
inclusion supplies monicity, so the original inclusion represents the dynamic
parabolic. Classical choice selects the resulting cocharacter and proof;
no canonical choice of cocharacter is claimed. Tests remain arbitrary,
including nonaffine and nonreduced schemes, and factorization on the original
test is never assumed.

`range_eq` exposes the full subgroup-functor equality. `quotient_fibers` rewrites
any supplied all-test right-coset fiber criterion using this equality. Its
quotient scheme `Q`, its projection `q : G.X → Q`, and both tested points
are unchanged. No geometric hypothesis on that quotient is required for the
rewrite, and it asserts no existence of sections or rational lifts.

When the ambient underlying scheme is affine, `modelIso` identifies the original
`P` with the existing chosen affine dynamic-parabolic representative. It applies
the published isomorphism between two representatives of the same subgroup
functor. `modelIso_hom_comp` and `modelIso_inv_comp` prove both exact commuting
equations with their inclusions into the original `G`. This is an actual group
scheme isomorphism and does not replace any supplied quotient model.

The provenance is internal: the construction combines the existing
pseudo-parabolic presentation, represented fppf-product trivial-factor theorem,
affine dynamic representability and uniqueness of representing models. The
split-radical product equality needed in the intended application remains a
separate structural obligation. This module supplies only the conditional
presentation adapter needed after a trivial split-radical reduction.
