# Coordinates on the full Whittaker-functional line

Author: Worker 181.

This is an internal linear-algebra adapter for the existing Whittaker predicates. For any field and any submodule of an arbitrary vector space, `scalarEquivOfNonzeroSpan` constructs coordinates on the entire submodule from a nonzero vector that spans it. The map from scalars to the submodule sends `c` to `c • w`; nonzeroness makes it injective, and the spanning hypothesis makes it surjective. The definition is the inverse of that linear equivalence. No ambient finite-dimensionality hypothesis is used.

`nonempty_scalarEquiv_iff` proves that a scalar equivalence exists precisely when an ambient nonzero vector belongs to the submodule and spans all its elements. In the forward direction, the inverse image of `1` is the generator and coordinates supply the multiples. In the reverse direction the construction above applies to the subtype. All ambient vectors in the submodule are quantified over.

`nonempty_standardFunctionalsEquiv_iff` specializes this equivalence to the whole space of standard Whittaker functionals. The existing `entrywiseCharacter_eq_standardCharacter` and `mem_functionals_entrywiseCharacter_iff` identify membership with the raw double product and upper-unitriangular condition of `InducedWhittakerTypeStatement`. It applies to all positive ranks, including rank one, with independent field and carrier universes. It makes no admissibility, irreducibility, or finite-generation assumption.

The adapter is derived directly from Mathlib's `LinearMap.toSpanSingleton`, `LinearEquiv.ofBijective`, and the published `Whittaker.EntrywiseCharacter` comparison. It supplies neither analytic heredity nor finite generation of induction. Its purpose is to connect the Library's scalar-equivalence formulation of full type to the existence-and-uniqueness formulation in the raw heredity statement.
