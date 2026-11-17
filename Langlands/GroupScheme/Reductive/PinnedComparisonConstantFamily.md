# The actual constant family of pinned comparison representatives

Let `M,N` be supplied affine pinned models, and let `S` be any common
scheme with maps `f : S → M.base` and `g : S → N.base`. This module
retains `AffinePinnedIsomorphismTheoremStatement` as an explicit input
`hAffine`; it does not prove that theorem.

`ComparisonLabel.localFamily d hAffine f g T` converts the canonical
actual representative with full lattice label `d` on `T` into an
all-test natural `LocalGroupIso` between the original groups over `S`,
parametrized by `T`. The direct/iterated pullback comparison equivalence
and `LocalGroupIso.ofBaseChangeIso` perform this conversion.
`localFamily_refine` proves compatibility with every relative refinement,
using arbitrary common-base naturality of the canonical representative.
`eq_of_localFamily_eq` shows that equality of these families at any
nonempty test determines the full label: it recovers the actual comparison
and applies full-character separation at the specified point.

`constantPinnedFamily M N hAffine f g` glues these representatives over
`GroupIsomorphismScheme.constantParameter S (ComparisonLabel M N)`, the
actual scheme coproduct of copies of `S` indexed by the full lattice labels.
It is defined with the generic constant-family construction, without an
isomorphism representer. `constantPinnedFamily_refine_injective` proves
injectivity on morphisms from every relative test. Equality of component
families implies equal labels if that test has a point. On empty tests
all morphisms agree, so no nonemptiness assumption on `S` or any test is
needed. The label type need not be finite or inhabited.

## Compatibility with normalization

`localNormalize_eq_of_normalized` takes any supplied
`RelativePinnedNormalization n`. If the actual direct comparison recovered
from a local family satisfies `n.normalized`, then its local-family
normalization equals itself. This is uniqueness of the normalized
representative in its own inner class, transported through the
actual/local-family equivalence.

`constantPinnedFamily_normalized` assumes that every labelled representative
on every relative test satisfies `n.normalized`. Under exactly this
assumption, every refinement of the actual constant family is fixed by
`n.actualNormalization.localNormalize`. A general morphism into the
constant scheme can have locally varying labels. Pulling back the
coproduct components provides a Zariski open cover; each restriction is
the corresponding representative family and is therefore fixed.
Naturality of normalization and descent of equality of all-test families
prove fixedness on the original test.

No local completeness of the label classification is asserted here.
The affine theorem and the normalization-predicate hypothesis above remain
explicit. There are no additional restrictions on the base or relative
tests, including connectedness, affineness, or reducedness.

## Provenance

This is an internal assembly of the full-character labels and canonical
fixed comparisons, using the already established direct/iterated comparison
and all-test coproduct interfaces. Its normalization argument follows
uniqueness and Zariski descent. The underlying representative construction
is conditional on the exact affine pinned theorem; the module does not
assert a new independent source theorem.
