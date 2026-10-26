# Actual normalized induced filtrations

This internal construction packages the published value filtration from
`Parabolic/InductionFactorMatchingProof` for an arbitrary supplied
`ObjectRepFiltration` of an actual Levi representation. It supplies the actual
induced filtration and equivalences of its graded representations, without
requiring simple graded pieces or finite length. It does not establish any
segment representation theorem or multisegment exhaustion.

For a block shape `B`, a representation `σ` of its actual Levi subgroup, and a
finite filtration `s` of `σ`, `normalizedInductionFiltration T B σ s` is the
filtration of the actual normalized upper parabolic induction. Its step at `i`
consists of smooth induced functions whose values lie in `s.subrepresentation i`.
The displayed step equality is definitional. Monotonicity and the zero and full
endpoints follow from the corresponding properties of `s` and the published
`Induction.valueFiltration`.

`nonempty_normalizedInductionFiltrationGradedEquiv` identifies an induced graded
quotient with the normalized induction of any smooth Levi representation `π`
equivalent to the corresponding quotient of `s`. It applies the published
`nonempty_valueQuotient_equiv_induced`, using the proved generic smooth induction
surjectivity theorem through
`normalizedInducedSurjectivity_of_smoothInductionSurjectivity`. Thus right
exactness is proved upstream, rather than supplied as a new assumption.

`normalizedInductionFiltrationGradedEquiv` chooses the equivalence with the
induction of the actual quotient itself. That quotient is smooth: its upper
filtration step inherits smoothness through its injective inclusion, and the
graded projection is surjective. Classical choice selects an equivalence from
the published nonemptiness result; no canonical formula for this selection is
claimed.

`exists_injective_normalizedInduced_graded` takes an actual injective
intertwiner from an irreducible representation into the induced ambient
representation. The published `ObjectRepFiltration.exists_injective_graded`
gives an injective map into one actual induced graded piece. Composing with the
chosen equivalence gives an actual embedding into the normalized induction of
the corresponding original quotient.

The field and all representation carriers have independent universes. The
induced carrier has the universe determined by the actual smooth induction
construction. The argument covers a filtration of length zero: the construction
still makes sense, and the embedding conclusion would require an element of
`Fin 0`, so its embedding hypotheses cannot hold.

The provenance is an internal assembly of existing constructions and proofs.
The used proof route consists of value subrepresentations, smooth induction
surjectivity, smoothness transfer, and irreducible embeddings into supplied
finite filtrations. It uses no classification conclusion, ordering theorem,
adjacent commutation, or linked-segment filtration.
