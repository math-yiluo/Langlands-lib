# Scalar restriction of associated coefficient sheaves

Author: Worker 13.

This module constructs the scalar restriction comparison for the actual
associated invariant sheaf. It uses an arbitrary Grothendieck site with binary
products, a genuine cover object with group action, a homomorphism of
commutative coefficient rings, and a coefficient sheaf with group action.
The site object and morphism universes are independent; rings, coefficient
module carriers and the group share universe `u`, as in `Associated`.

Restriction of module scalars preserves limits. The corresponding functor on
module sheaves preserves the single-object group limit because forgetting to
presheaves creates limits, and presheaf scalar restriction preserves them
pointwise. Product sections and inverse-deck diagonal diagrams have unchanged
section data. The natural comparison `associatedRestrictScalarsIso` is the
limit-preservation isomorphism followed by the isomorphism of these diagrams. Its naturality is part of the constructed
natural isomorphism, for every equivariant morphism of coefficient sheaves.
The `hom_inclusion` formula characterizes the forward comparison: composing
with the restricted-coefficient invariant inclusion gives the scalar
restriction of the original inclusion. The `inv_inclusion` formula gives
the inverse normalization. These formulas follow from the limit projections
and the inverse-isomorphism law, respectively.

This is an internal categorical consequence of `Associated`, Mathlib's
`ModuleCat.restrictScalars`, sheaf composition, and preservation of limits.
No sheafification hypothesis is needed for this restriction comparison. No
flatness, finite-group, topology, covering, or torsor hypothesis is imposed.
The result compares arbitrary sheaf coefficients; it does not assert that
tensor extension commutes with invariants or construct local trivializations.
Compatibility of constant sheaves with scalar restriction, the actual Harris
specialization, and comparison maps for scalar extension are separate work.
