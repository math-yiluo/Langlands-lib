# Collapse finite framed comparison chains to actual comparisons

This module identifies the already constructed comparison-chain relation
and quotient with existence of a single actual framed comparison. It uses the
actual identity, inverse and product-cover composition constructions, and
preserves the original definitions of `ChainEquivalent` and `ComparisonClass`.
It asserts no identification with an original-source moduli functor.

`directlyComparable_refl`, `DirectlyComparable.symm` and
`DirectlyComparable.trans` prove that existence of the actual comparison is an
equivalence relation. A comparison retains actual refinements of the original
target atlases, a full-order formal isomorphism, equality of the stored residue
maps and the actual quotient framing square. Transitivity uses exactly the
constructed `Comparison.trans`, with the actual common product covers and its
proved framing certificate.

`ChainEquivalent.directlyComparable` inducts on the finite reflexive transitive
chain. The empty chain is witnessed by `Comparison.refl`; the tail step composes
the induction witness with the given next actual comparison. Thus the resulting
single witness still compares the original endpoint targets. The converse is
the existing singleton-chain construction. This proves
`chainEquivalent_iff_directlyComparable` and, using the existing quotient
equality theorem, `comparisonClassOf_eq_iff_directlyComparable`.

`Comparison.ofClassEq` uses classical choice on this proved nonempty type of
actual comparisons. It does not assume a comparison as extra data or recover one
from an arbitrary point-functor equivalence. For an actual representative of a
given class, `ComparisonClass.comparisonToRepresentative` applies this exact
criterion to the existing chosen representative equation.
`comparisonFromRepresentative` is the actual inverse of that chosen comparison.
No uniqueness of comparisons or canonical refinement is asserted.

The parameters retain the local field `K`, finite-dimensional central division
algebra `D`, field `L` and its embedding into `D`, coefficient ring `R`, residue
field `κ`, fixed height-certified frame `Φ`, and one Nilp object in universes
`{v,u}`. Original covers may differ and need not be finite; quotient scalar maps
may merge generators. This module resolves the finite-chain-collapse boundary
recorded in `DrinfeldFramedClasses`. Varying-base framed functoriality, group
actions, polarizations, descent, levels, source-functor identification and
representability remain separate.
