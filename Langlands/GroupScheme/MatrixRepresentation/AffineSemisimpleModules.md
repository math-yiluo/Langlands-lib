# Actual semisimplicity and the affine operator module

This internal interface supports Milne, *Algebraic Groups* (2017),
Proposition 4.19, pp. 90–91 (`milne-2017-algebraic-groups`). The semisimplicity
formula is precisely the sum of nonzero simple actual stable subspaces used by
the published target.

Every stable ground-field subspace has the inherited operator-algebra module
structure, named `operatorSubmodule`. Restricting scalars recovers the same
subspace. A simple module subspace is exactly a nonzero minimal actual stable
subspace, since these operations preserve the underlying sets and inclusion.
Restriction of scalars also preserves arbitrary suprema, so the raw sum formula
for actual semisimplicity is equivalent to `IsSemisimpleModule` for the operator
algebra.

The finite decomposition theorem uses Mathlib's independent family of simple
submodules of a semisimple module. Restricting scalars preserves independence and
the spanning supremum. Finite ground-field dimension forces the nonzero
independent family to be finite; reindexing by `Fin r` gives the stated finite
family. No coordinate basis or direct-sum representation is chosen in this
module. All results apply to arbitrary affine group schemes, including
nonreduced ones.
