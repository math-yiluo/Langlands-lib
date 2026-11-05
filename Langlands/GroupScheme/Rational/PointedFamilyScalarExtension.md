# Smooth universal sources and scalar extension

This internal adapter compares actual nested commutator sources and their whole
basepoint sections after an arbitrary change of base scheme.

`source_smooth` uses induction on the source recursion and smoothness of binary
products over the base. It assumes smoothness of both the initial source and
the original group.

`sourceBaseChangeIso` uses the identity isomorphism at index zero and the
inverse tensor comparison of the actual pullback functor at every successor.
`parametersBaseChangeIso` uses the inverse terminal comparison at index zero
and the same tensor comparisons thereafter. Thus no parameter or terminal
factor is discarded.

`basepointSection_baseChange` identifies the pullback of the entire original
section with the entire section formed from the transported basepoint. The
basepoint is transported by the terminal comparison followed by its pullback.
The proof uses cancellation of the terminal comparison at zero and naturality
of the tensor comparison at each successor.

`family_eq_one_of_smooth_of_rationalPointStatement` applies the conditional
smooth-scheme rational-density adapter over a separably closed field. Smoothness
of the nested affine-line source also gives reducedness. The earlier
whole-section family constancy theorem then proves that a map to a separated
wound target is the identity whenever its entire basepoint section is the
identity. The exact published algebraic rational-point proposition remains an
explicit argument.

These are internal deductions from the existing actual source recursion,
the monoidal structure of scheme pullback, smooth-product and reducedness
theorems, and the conditional density adapter. They do not prove the algebraic
rational-point proposition or a structural decomposition of unipotent groups.
