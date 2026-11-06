# Pointwise use of supercuspidal extension

Author: Worker 422.

This supporting helper module derives pointwise extension facts from the existing
class-space definitions. It supplies the irreducible-Weil case of a possible
assembly characterization induction. It does not prove assembly existence,
assembly extension, or either characterization statement. Its field, parameter,
and automorphic carrier universes remain independent.

`parameterForget_injective` uses the fact that the Frobenius-semisimple
parameter quotient has the same pair-isomorphism relation as the unrestricted
quotient, restricted to the objects with the parameter property. Quotient
induction therefore reflects equality of the unrestricted classes. Equality of
the rank-indexed subtypes follows by subtype extensionality.

`IsZeroMonodromyOf.unique` takes two representations of the same irreducible
Weil class from the supplied zero-monodromy certificates. Equality of their Weil
classes gives an actual intertwining linear equivalence. The same equivalence
commutes with their zero monodromy maps, so it gives equality of the two
underlying pair classes. Injectivity of `parameterForget` gives equality of the
parameter classes.

`ExtendsSupercuspidal.apply_of_zeroMonodromy` chooses the parameter promised
by the existing existential extension predicate, identifies it with the supplied
one by uniqueness, and rewrites the promised image equality.
`ExtendsSupercuspidal.eq_on_irreducible` applies that result to two extensions
using the irreducible Weil class supplied by `IsIrreducibleWeilParameter`.

These are internal consequences of the current quotient and correspondence
definitions. Their provenance is the published Lean definitions, without an
additional literature assertion or assumption.
