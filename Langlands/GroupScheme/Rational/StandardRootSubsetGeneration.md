# All-test generation of dynamic centralizers and radicals

This internal supporting module develops generation lemmas for the proof of
`StandardParabolicRootSubsetGroupStatement`. Its centralizer argument applies
the published nonnegative-root parabolic generation theorem inside the dynamic
centralizer, where the cocharacter is central and its parabolic is the whole group.
The closed competitor is intersected with that centralizer; no smoothness
assumption is placed on the competitor.

The indivisible-ray lemma applies the published positive-ray descent to either
the generic cocharacter or its negative. The radical containment lemma uses the
published ordered product isomorphism and its ambient multiplication equation
to transfer factor membership to membership of the product on every test scheme.

These are derived implementation lemmas, using the published constructions and
proofs named in the Lean imports.
