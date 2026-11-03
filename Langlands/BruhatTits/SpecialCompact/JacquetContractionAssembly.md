# Assembly of the existing Jacquet contraction predicate

This internal helper module derives the seven fields of
`Langlands.Jacquet.IsIwahoriContraction` from the literal-intersection clauses
of the simultaneous-basis interface. It constructs no strict-chamber element.
Its abstract subgroup and set parameters are the parameters already used by
`SmallSubgroupPredicates` and `ContractionPredicates`.

`InheritedCompactOpenNormalBasis.exists_intersection_le` applies the inherited
identity-neighborhood basis to a prescribed open subgroup of the Levi. The
definition of `intersectionFamily` then recovers a member of the same ambient
family whose literal preimage under the Levi inclusion is contained in that
open subgroup.

`isIwahoriContraction_of_contractionAndCofinality` takes a specified element
of the Levi, the section, the weak chamber and the strict chamber. The
ordered multiplication bijection supplies the factorization field by
surjectivity. Weak chamber contraction gives the forward and opposite
inclusions. Levi normalization gives the inverse Levi inclusion by solving
the conjugation equality. The strict expanding union gives the pointwise
entry exponent. The opposite contracting-power neighborhood basis is applied
to the preimage of an arbitrary ambient open subgroup. Its ambient containment
clause ensures that all conjugated points lie in the opposite radical,
so the resulting exponent works uniformly for the entire literal intersection.

The mathematical provenance is derived packaging of Renard,
*Représentations des groupes réductifs p-adiques*, 9 July 2026 edition,
V.5.2(ii)–(iv), printed123/PDF129. This helper uses the published definitions
directly. Existence of a strict element in an actual compatible split component,
and existence of the simultaneous basis itself, are separate obligations.
