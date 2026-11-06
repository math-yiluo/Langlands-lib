# Compact fixed vectors under coefficient specialization

This internal adapter takes a smooth complex representation with a commuting
coefficient action, a smooth complex target, and a complex intertwiner with the
semilinear scalar law of the given coefficient-ring map to the complex numbers.
It constructs the full tensor specialization and the canonical tensor map on
actual subgroup fixed vectors.

For a compact open subgroup, normalized compact averaging is coefficient-linear
by naturality for multiplication by each coefficient. It is a retraction of the
actual fixed inclusion. Tensor extension preserves this retraction. If the full
specialization is bijective, its restriction to the tensor of fixed vectors is
injective by the split inclusion, and surjective by averaging a full preimage.
This gives a canonical complex linear equivalence without a flatness assumption.

The actual compressed action, viewed coefficient-linearly, has the same pointwise
powers as the original complex action. Compression naturality on pure tensors
shows that all powers intertwine under fixed specialization. The base-change
stability lemma and the fixed equivalence transfer a supplied stable exponent
without changing it. The coefficient ring, acting group and both carriers have
independent universes; no finite generation is needed.

This supporting result retains full-specialization bijectivity as an explicit
hypothesis. It proves neither that hypothesis for induced families nor family
finiteness nor an exponent uniform over all representations. Its provenance is
the published compact averaging, compression naturality, tensor extension and
stable-equivalence constructions, with the compatible coefficient action and
scalar-extension stability adapters. No new external theorem is invoked.
