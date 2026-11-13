# Root directions under torus restriction and field descent

This internal helper for Task 6016 is derived from the Library's actual
adjoint-root restriction, split-torus character base change, and real lattice
pairing. It isolates the root-direction part of
`UnramifiedRootJumpDescentStatement`; it supplies no filtration-jump witness.

Let `k ⊆ K` be any field extension, `G` an affine group scheme locally of
finite type over `k`, and `f : S → T` a map from a split torus such that
`f ≫ iT = iS`. No reductivity, maximality, Galois action, valuation, or
characteristic hypothesis is used.

`exists_rootForm_comp_torusFieldTranslationMap` takes a relative root `β`
of `T_K` in `G_K` whose root form has nonzero pullback along the published
`torusFieldTranslationMap`. It produces an actual relative root `α` for
`iS` whose form, composed with the lower quotient map, equals that pullback
as a real linear map. Thus the two forms have equal kernels.

The proof descends the restricted character `f_K ≫ β` through
`characterLattice.baseChangeEquiv` of the split torus `S`. The evaluation
identities `eval_descentCocharacterMap` and
`eval_splitCocharacterBaseChange` identify its real form with the specified
pullback. Nonzero pullback implies a nonzero restricted character.
`rootRestriction` then proves upper root membership for the restricted
action, and `mem_roots_baseChange_iff` reflects it to root membership over
`k`. Evaluation through the quotient defining `rootForm` gives the claimed
equality.

`torusFieldRootOfNonzeroForm` chooses such an actual lower root;
`torusFieldRootOfNonzeroForm_spec` records its exact form equality.

`exists_rootForm_comp_of_affineRoot` applies this result to the actual
relative root supplied by the definition of an ordinary affine root of
any supplied upper apartment, with the monomorphism instance needed to
define that apartment. It asserts equality of forms, with no
assumption on the value of the affine root at a point.

These are derived interface lemmas, not numbered assertions attributed to
the literature. All inputs are published Library results; the target
statement is imported only for its general `torusFieldTranslationMap`
definition. The arithmetic assertion that a lower rational root-group
element attains a specified value remains a separate obligation.
