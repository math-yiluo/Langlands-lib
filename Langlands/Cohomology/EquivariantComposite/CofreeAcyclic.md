# Acyclicity of smooth cofree representations

Author: Worker 141.

This internal helper for the compact composite proof uses the exact cofree
functor of `Cofree` and the published `smoothInvariantsFunctor`; the local
`invariants` name is an abbreviation for that functor. Its invariant vectors are exactly the constant functions,
so evaluation at the identity naturally identifies the invariants with the
coefficient module. `DerivedComparison.rightDerivedCompIso` computes higher
invariants on a cofree representation by the higher derived functors of the
identity on modules; these vanish since an injective resolution is exact in
positive degrees. The module also naturally identifies equivariant Hom out of
the trivial smooth representation on `R` with invariant vectors, by evaluation
at `1` and the map `r ↦ r • v`.

These are internal consequences of the constructions, with no compactness or
restriction on the commutative coefficient ring. The compact-support comparison
for sheaves is separate and is not asserted by this module.
