# Positive-rank irreducible actual automorphic operator quotients

This internal derived construction refines the published actual
`OperatorSubquotient`. The number field `F : Type uF` has arbitrary universe,
the coefficients are complex, and the index `r : ℕ` denotes general linear
rank `r + 1`. No compactness assumption is required for the irreducible
quotient objects or their classes. The final bridge from cuspidal realizations
retains their existing explicit `CompactSpace (AdeleQuotient F)` hypothesis.

`IrreducibleOperatorSubquotient F r` retains an actual invariant numerator
inside stable automorphic forms, an actual whole-operator invariant
denominator in that numerator, and irreducibility of their genuine module
quotient. Its carrier and representation are the existing actual quotient
and its induced action of the complete concrete operator algebra. They are
not arbitrary replacement data. Through the stored subquotient, the object
retains the published canonical projection, finite and standard compact
restrictions, genuine enveloping differential action, and smooth finite
and whole-carrier local restrictions.

Irreducibility means simplicity of the order of all whole-operator invariant
subspaces, including nontriviality. Mathlib's simple monoid-algebra module
and its carrier equivalence therefore prove `space_nontrivial`. The published
quotient invariant-subspace correspondence proves `lower_isCoatom`: the
actual denominator is maximal proper among invariant subspaces of the
actual numerator. In particular it is not the whole numerator.
`ofCoatom` constructs the actual quotient object directly from a supplied
numerator and such a denominator; it does not assume the desired quotient
representation or a comparison equivalence. The supplied maximality
condition is explicit, and the construction does not prove that a maximal
proper denominator exists. A nonzero quotient vector and surjectivity of
the canonical projection give an actual numerator representative outside
the denominator.

`Equivalence` is a genuine complex-linear representation equivalence for
every concrete operator. `IsoClass` quotients the actual irreducible
presentations by existence of such an equivalence. Class equality is exactly
this representation equivalence relation, rather than equality of
numerator/denominator presentations. Forgetting irreducibility constructs an
injective map and bundled embedding into the published whole-operator
quotient classes, since both quotients use the same equivalence relation on
the selected objects. `finiteClass` composes this with the published finite
smooth class map. It does not assert irreducibility or injectivity after
forgetting operators. Every class has an actual irreducible quotient
representative by quotient surjectivity.

`PositiveRankIrreducibleSubquotientClass F` is the dependent sum of the
fixed-rank classes. Its rank is its index plus one, and hence positive.
Fixed-rank insertion is injective, preserves the displayed rank, and for
actual objects has the same whole-action equivalence criterion. Distinct
ranks give distinct classes in this dependent sum.

For a supplied `CuspidalOperatorRealization F r`, `toIrreducibleSubquotient`
takes its existing actual numerator and the zero denominator. The published
zero-denominator irreducibility theorem proves the required property.
`toIrreducibleSubquotientEquiv` is the actual canonical quotient projection
equivalence; its formula on every represented vector is proved. The
published zero-denominator equivalence reflection identifies equivalence
of these new quotients with equivalence of the original cuspidal
realizations. It therefore constructs a well-defined injective class map
and bundled embedding. Forgetting to general quotient classes agrees with
the published zero-denominator bridge, and the new embedding commutes with
forgetting to the actual finite smooth representation class.

Provenance is internal: the actual quotient construction, its invariant
subspace correspondence, simple-module nontriviality, and the canonical
zero-denominator equivalence give the results above. The class and rank
constructions follow the existing cuspidal-realization class conventions.
Only published prerequisites are imported; neither pending image nor
subspace-presentation candidate is used. No new identification with original
literature is asserted.

This module supplies an irreducible refinement of actual automorphic
quotients and a faithful bridge from already supplied cusp realizations.
It does not assert existence of an irreducible quotient, admissibility,
unitarity, local tensor-factor selection, isobaric assembly, or spectral
existence. Quotient vectors are not evaluated as functions and receive no
quotient topology here. General irreducible quotient classes are not
asserted cuspidal, and no converse asserting that a general quotient class
has an embedded cuspidal representative is supplied.
