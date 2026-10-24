# Nonzero finite invariant subspaces of actual cuspidal realizations

This internal construction works over a number field `F : Type u`, with
complex coefficients and the same explicit compactness assumption on the
additive adele quotient as `CuspidalOperatorRealization`. The actual rank is
`r + 1`.

`CuspidalOperatorRealization.FiniteSlice S` consists of an actual finite
adelic invariant form subspace, its containment in the finite image of `S`,
and its nonzeroness. It is data inside the realized space, before passage to
isomorphism classes. The word slice here means a selected finite invariant
subspace; it does not assert a tensor decomposition or a fixed
archimedean factor. In particular, full-operator irreducibility does not
silently become irreducibility of the finite restriction.

The whole finite image is a canonical example, using the proved nonzeroness
of the cuspidal realization. The finite orbit span of any specified
nonzero full-realization vector is another example. Its containment follows
from the existing minimality theorem for the orbit span, and its
nonzeroness follows from injectivity of the actual form inclusion.
Every slice has a nonzero actual vector: otherwise its inclusion into
forms would show that the entire subspace is bottom.

Cuspidality and a prescribed central-character condition are inherited by
containment of actual form subspaces. The slice inclusion into the whole
finite image is explicitly a faithful finite intertwiner.

For a full-operator equivalence between two actual cuspidal objects,
`transportMap` composes this inclusion with the published equivalence of
the whole finite images and the target's actual form inclusion.
The map is injective as a composition of injective maps. Its invariant
range constructs a new slice inside the target; a nonzero source vector
proves that this range is nonzero. The existing injective-image
construction gives `transportEquiv`, a genuine finite representation
equivalence with a proved formula for inclusion in forms. Hence the
transported slice has the same finite smooth class.

The target slice is cuspidal by its containment in the target's cuspidal
image. This uses both objects' actual cusp witnesses; it makes no assertion
that arbitrary isomorphic embeddings have the same constant terms.
Likewise the character inheritance theorem requires the character
condition on the chosen containing object.

The provenance is internal: invariant orbit spans, subspace inclusions,
actual equivariant images, and the existing full-to-finite equivalence.
No new identification with original literature is asserted. No finite
irreducible slice, tensor presentation, spectral data, independence of
slice choice, or descent to full cuspidal classes is constructed here.
Those further existence and uniqueness obligations remain separate.
