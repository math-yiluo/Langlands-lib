# Compact lifting through the actual central integral

This internal unit isolates the equivariance and compact averaging used in
Waldspurger (2003), VIII.5, printed p.332 (PDF p.98). The source deduces
same-level containment from Theorem VIII.4.2 and two-sided equivariance.
The present argument supplies the averaging behind that deduction.

The group is an arbitrary topological group. Its Schwartz space is the
published `Space Ξ σ`, with `TranslationWeights` ensuring that actual
two-sided translations preserve the space. The central subgroup and its
measure and character are the literal inputs to `centralProjection`.
The theorem does not rescale that measure.

`centralProjection_translate` proves pointwise commutation with both
translations directly inside the defining integral, using centrality. It
needs no convergence or interchange of integrals. The all-translates,
integrable cuspidal condition is also invariant under translations by
reassociating the two outer group elements.

`Space.translationRepresentation` is the actual action of the product
group on Schwartz vectors. Each vector has a compact open bi-invariance
level, so this representation is smooth. A stable subspace inherits the
same representation and smoothness.

`exists_biInvariant_central_preimage` assumes absolute convergence on a
translation-stable Schwartz subspace. This makes the raw central integral
a linear map on that subspace. For a bi-invariant function in its full raw
image, it averages a chosen preimage over the compact open product
subgroup. The published `Compact.averageMap` is the normalized finite
orbit mean: the orbit is finite because the representation is smooth and
the subgroup compact. Its normalization is the inverse of the nonzero
finite orbit cardinality. Thus no infinite vector integral or unproved
exchange of integrals is involved. The averaged vector is bi-invariant.
Equivariance and invariance of the given image make the central linear
map constant on the orbit, and the published finite-mean lemma shows that
its value at the average is exactly the original function.

This is an auxiliary lifting result with explicit convergence and
translation hypotheses, not a proof of the closed VIII.4.2 equality or
closed coefficient-lifting target. A rational-point application must
still prove translation stability of the actual cuspidal submodule and
supply its central convergence.
