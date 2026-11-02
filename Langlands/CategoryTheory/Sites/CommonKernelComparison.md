# Comparing sheaves with a common kernel

This is an internal derived helper for comparing presentations of sheaves on
the same site. It generalizes the effective epimorphism argument in the
published `AlgebraicSpace.FppfQuotientRepresentability` from a scheme quotient
to two arbitrary type-valued sheaves.

For a Grothendieck topology `J`, suppose type-valued sheafification exists.
Let `a : H ⟶ F` and `b : H ⟶ G` be locally surjective maps of sheaves.
Assume that at every object, two sections of `H` have the same image under
`a` if and only if they have the same image under `b`.
`exists_iso_of_isLocallySurjective_of_same_kernel` produces an isomorphism
`e : F ≅ G` satisfying `a ≫ e.hom = b`.

The implemented proof uses local surjectivity to obtain epimorphisms and
Mathlib's regular epimorphism theorem for type-valued sheaves to make both
maps effective epimorphisms. Evaluating an equality of sheaf morphisms at
every object and section transfers the equality along the common kernel
condition. Effective epimorphism descent constructs maps in both directions.
Their factorization equalities and epimorphism cancellation show that they
are inverse.

This lemma assumes both codomains are sheaves for the same topology. It
constructs no scheme quotient and proves no change-of-topology descent
theorem by itself. Its provenance is the generalization of the published
common-kernel helper above and Mathlib's effective epimorphism and sheaf
infrastructure.
