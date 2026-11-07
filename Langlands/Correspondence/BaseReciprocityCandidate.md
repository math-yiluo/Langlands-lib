# The actual base component of a supplied reciprocity family

Worker 1555 derives this internal construction from the existing canonical
bottom-field unit equivalence, the actual base Weil equivalence and the
functorial equivalence on quotients by closed commutators. No new
original-literature assertion is introduced.

`baseReciprocityCandidate` composes three actual continuous multiplicative
equivalences: from the standalone Weil abelianization to the bottom-field
Weil abelianization, the supplied family's bottom component to bottom-field
units, and the canonical bottom-field unit equivalence to the original field's
units. The bottom field's fixing subgroup is the whole Galois group, so the
underlying `baseWeilEquiv` only rebrackets the same actual Weil elements.
No algebraic-closure lift is chosen in this construction.

`baseReciprocityCandidate_spec` proves the unchanged `IsBaseReciprocity`
predicate by evaluation on quotient generators. The two resulting maps agree
by their definitions. The existing base-candidate uniqueness theorem then
proves that exactly one compatible standalone candidate exists, and the
corresponding equivalence with equality to the constructed candidate.

For a supplied normalized family,
`normalizedAbs_baseReciprocityCandidate` evaluates its normalization law at
the bottom-field abelianization projection of an actual base Weil element.
The specified base degree is unchanged by rebracketing. Canonical normalized
absolute-value transport along the actual bottom-to-base p-adic algebra
equivalence converts this to the original field's absolute-value formula.

`geometricOrder_baseReciprocityCandidate` proves equality between order after
the constructed candidate and the original descended geometric degree.
Quotient induction reduces to actual Weil elements. The normalized
absolute-value formula expresses both sides as integer powers of the same
base residue cardinality. Since that cardinality is greater than one,
integer-power injectivity identifies the orders, with the original positive
geometric-degree sign. `geometricOrder_of_isBaseReciprocity` transfers this
property to every compatible candidate by their proved equality.

The prime and field universe are arbitrary. The family remains a supplied
input, and its normalization is a premise only for the normalization theorems.
This unit constructs no family or local-constant system and asserts no
unconditional reciprocity existence. The order relation proved here is only
one conjunct of `IsGeometricReciprocity`; its full normalized finite
norm-residue condition is not proved here. No analytic comparison or closed
supercuspidal correspondence is concluded.
