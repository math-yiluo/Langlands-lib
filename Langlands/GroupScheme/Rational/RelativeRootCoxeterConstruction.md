# A Coxeter system from the given relative root system

This internal construction starts with the exact `HasRelativeRootSystem i`
predicate and splitness of the actual torus. It relabels the finite root pairing
witness by actual relative roots, and identifies the base of the cocharacter
evaluation functional with the actual `SimpleRoot i ν` labels. Injectivity of
rationalization of split-torus characters identifies both positive roots and
their additive decompositions. This root/base relabeling is valid for any
cocharacter `ν`.

The Coxeter-system theorem additionally fixes
`hν : IsGenericCocharacter i ν`: the integer pairing
`latticePairing T α ν` is nonzero for every actual relative root `α`.
This makes the cocharacter evaluation functional nonzero on every witness
root, supplying the regular-functional hypothesis of the proved
`rootPairingWeylCoxeterStatement_proof`. That theorem supplies a finite
Coxeter system on the witness Weyl group. Its faithful linear image equals that of the actual
scheme quotient by the definition of `HasRelativeRootSystem`. Transport through
this equality and through the base-label equivalence gives one Coxeter system
on the actual quotient, with simple generators that are `IsRelativeReflection`
on the rational root span. Its right-length criterion is positivity of the
actual simple character image. The proof preserves all labels, includes empty
root systems and permits nonreduced systems.

This construction establishes a root-span reflection law and the length
criterion. It does not supply integral coroots, a full-character reflection law,
standard Levi Weyl identification, or the stronger
`IsRelativeWeylCoxeterRealization`. The proof is an internal transport of the
published root-pairing Coxeter theorem, not an additional structural assumption.
