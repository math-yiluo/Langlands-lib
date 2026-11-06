# Restriction to the unitary Jacquet part

This supporting construction implements the characteristic-space and extension
algebra used in Renard 2026 VII.2.4, Proposition, printed p.229 / PDF p.235.

A Levi intertwiner preserves the generalized split-component weight equations:
the actual Levi-point equivalence identifies its action with the action on the
literal Levi image. A nonunitary weight maps to zero in a tempered target by
`tempered_generalizedWeightSpace_eq_bot`. Taking the supremum proves vanishing
on the entire nonunitary Jacquet part. This does not require temperedness of
the source representation.

The two actual Jacquet parts are transported to invariant subspaces for the
Levi-point action. Given their complementarity, the existing
`SmoothRep.complementaryDesc` construction extends a map on the unitary part
by the zero map on the nonunitary part. Its restriction is the original map.
Extending the identity gives an actual retraction onto
`leviUnitaryJacquetModule`.

The definition `leviUnitaryJacquetRestrictionEquiv` has restriction along the
published `leviUnitaryJacquetModuleι` as its forward map and extension by zero
as its inverse. To recover an original map from its restriction, the proof
decomposes each vector uniquely into a unitary and a nonunitary component.
The original map and the extension agree on the first component; both
vanish on the second. The other inverse law is the restriction identity for
`SmoothRep.complementaryDesc`. The final bijectivity lemma exposes exactly
the precomposition map used by `TemperedJacquetUnitaryRestrictionStatement`.

This is a derived implementation of the characteristic-space argument of
Renard VII.2.4, using the Library's actual normalized Jacquet objects and
Levi-point transport. The target is normalized-exponent tempered; the source
may be arbitrary. Complementarity remains an explicit premise of the
extension, retraction and equivalence. The vanishing lemmas do not need it.
No unconditional VII.2.3 or VII.2.4 task theorem is claimed here.
