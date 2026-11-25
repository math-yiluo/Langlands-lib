# Actual finite almost-simple products for simply connected groups

The Lie-dimension induction adapts the preexisting published proof in
`AlmostSimpleRationalGenerationReduction`. The data interface and product
construction are new in this module.

This internal construction supports the Weil-restriction structure proof
(`simplyConnectedAlmostSimpleWeilRestriction`, in
`AlmostSimpleWeilRestrictionProof`). `SimplyConnectedAlmostSimpleProduct G` contains a finite index
type in the ground field's universe, an actual group scheme for each index,
proofs that each is simply connected and almost-simple, and a group-scheme
isomorphism from `G` to their categorical product. The empty product is
allowed. The construction works over every field and in every characteristic.
It does not assert absolute almost-simplicity, uniqueness, a Galois action,
or descent of a selected factor.

`IsSimplyConnected.almostSimpleProduct` constructs these data. Its existence
proof uses strong induction on the published Lie dimension of a smooth
connected affine group. If the full point functor is trivial, it uses the
empty product; if the group is almost-simple, it uses a one-factor product.
Otherwise the negation of almost-simplicity supplies a proper nontrivial
smooth connected closed normal subgroup. The published unconditional
`semisimpleNormalIsogenyComplement` supplies a commuting semisimple normal
complement, with central-isogeny multiplication. Simple connectedness makes
this multiplication an isomorphism. The published direct-factor lemmas make
both factors simply connected, and both proper closed inclusions strictly
decrease Lie dimension. The induction hypotheses give finite product
presentations for both factors. `finiteProductSumIso` combines these using
the disjoint union of the finite index types.

The data type, its empty/single/append constructors, and the disjoint-union
product isomorphism are implementation interfaces derived internally from
categorical products. The induction argument follows the published
`simplyConnectedAlmostSimpleRationalGeneration_of_normalIsogenyComplement`,
but retains actual product presentations instead of proving a generation
property of rational points. This is not a proof of the Weil-restriction
target. The structural background for the remaining geometric and descent
steps is CGP, *Pseudo-reductive groups*, second edition (2015),
Proposition A.5.14, printed pp.519–520 / PDF pp.545–546, registered as
`conrad-gabber-prasad-2015-pseudo-reductive`.
