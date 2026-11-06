# Coherence of the base reciprocity component

This is an internal construction and quotient calculation using the existing
common-closure correspondence definitions. It does not invoke a reciprocity
existence or uniqueness theorem.

The subgroup fixing the bottom intermediate field is the whole absolute
Galois group. Its preimage in the actual local Weil group is therefore the
whole Weil group. `baseWeilEquiv` constructs the continuous multiplicative
equivalence with this bottom-field subgroup by retaining the same element.

If two candidates satisfy `IsBaseReciprocity` with the same common-closure
family, their values on every Weil element agree by the two base-component
identifications. Quotient induction then gives equality on the Weil
abelianization, hence equality of the candidates. The final theorem expresses
this as an equivalence: after one base candidate is identified, identifying
another candidate is exactly proving that the candidates are equal.

These results supply coherence for a fixed family. They do not prove that
arbitrary geometrically normalized candidates are equal, nor do they prove
epsilon-factor inheritance.
