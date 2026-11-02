# Exactness of invariants under all-module acyclicity

This internal unit extends the preceding invariant-module helpers. For a
ring étale equivalence relation, assume that every coaction in a fixed
module universe is acyclic in the published sense.

`IsHom.of_comp_injective` shows that an equivariant injection reflects
equivariance of a map into its domain. Source flatness makes the tensor
of that injection injective, so the equivariance identity can be checked
after applying it.

`kernelLift` restricts the first linear map of an exact sequence to the
kernel of the second. `kernelLift_subtype` records its factorization.

`invariantsMap_exact_of_acyclic` treats equivariant maps
`M → N → P` with `range i = ker p`. It requires neither injectivity of
`i` nor surjectivity of `p`. The proof constructs the kernel coaction
of `p`, factors `i` through that kernel, and checks equivariance of the
factor using the preceding reflection lemma. The range/kernel equality
makes the factor surjective, so all-module acyclicity makes its invariant
map surjective. An invariant element of `N` killed by `p` is invariant in
the kernel because the injective kernel subtype reflects invariance.
Lifting it along the factor proves exactness. The other inclusion uses
the original range/kernel equality.

Source flatness follows from the source map's étaleness. All modules and
the kernel lie in the same universe, as required by the unchanged
acyclicity predicate. The ring universe is independent. The derivation
uses no geometric quotient or descent conclusion and does not establish
the full Serre criterion.
