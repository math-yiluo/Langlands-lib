# Full-operator equivalences of actual automorphic realizations

This internal construction uses `OperatorRealization`: actual invariant complex
subspaces of the constructed stable automorphic function space. The number field
has arbitrary universe, and the rank is any natural number.

`operatorAction` retains the complex algebra structure of the entire restricted
concrete operator action. Its value is the existing representation; zero,
addition and scalars are checked through the two subtype inclusions to actual
finite-smooth functions. Its generator values are exactly finite adelic
translation, standard infinite compact translation and the genuine enveloping
differential action.

`intertwines_iff_generators` says that a complex linear map commutes with every
element of the concrete operator algebra if and only if it commutes with those
three families. The forward direction specializes the algebra element. The
reverse direction uses induction over the generated subalgebra: linearity
handles scalar and sum operators, and two successive intertwining identities
handle a product in its composition order.

`Intertwiner` and `Equivalence` reuse Mathlib's intertwining maps and equivariant
linear equivalences for this entire algebra's multiplicative action. Consequently
they inherit its identity, composition, inverse and transitivity operations.
The module proves the three generator equations for intertwiners and constructs
intertwiners or equivalences from those equations. All equations concern the
actual restricted actions, not actions supplied independently as data.

Forgetting compact and differential operators gives a finite intertwiner or
finite equivalence with the same underlying map. `Equivalence.finiteImage`
composes this with the two existing equivalences to actual finite form images.
Its evaluation theorem identifies the image of every realized vector.

`IsoClass` is the quotient of actual realized subspaces by nonempty full
equivalence. The setoid laws use the identity, inverse and composite equivalences.
`isoClass_eq_iff` identifies equality exactly with the existence of a
full-operator equivalence. `IsoClass.finiteClass` is a well-defined map to the
existing finite smooth representation classes, because a full equivalence
induces the finite-image equivalence. No injectivity of this forgetting map is
asserted.

The construction does not identify different embeddings as equal subspaces.
It neither transfers their embedded cusp or central-character predicates nor
constructs irreducible or cuspidal occurrences, nonzero forms, the complete
automorphic subquotient category, tensor factorization or canonical spectra.
Equality of the stable core with all forms still has its existing analytic
preservation obligations.

All content is derived internally from the concrete published operator and
realization constructions, Mathlib algebra induction, equivariant linear
equivalences and quotients. There is no new original-literature identification
or theorem invoked.
