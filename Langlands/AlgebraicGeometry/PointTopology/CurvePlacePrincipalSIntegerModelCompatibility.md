# Original field and integer points of the actual curve S-integer Weil model

This derived construction supplies the local field comparison and its integral
compatibility for Conrad, *Weil and Grothendieck approaches to adelic points*
(2011), Example 4.2, printed page 10.

Use the actual lower S-integer ring at a principal exceptional set and the
actual upper S-integer ring at its full place preimage. These principal sets,
the poles of a parameter together with the poles of the inverse of a nonzero
normalized-chart denominator, form the previously proved cofinal family.
For a locally finite type upper model Y with an actual relative projective
immersion, `curvePlacePrincipalSIntegerModelFieldPointHomeomorph` identifies
completed-field points of the actual lower relative Weil scheme with the
product of Y's points at every original upper completed field above the chosen
lower place. This field comparison holds at every original lower place,
without an outside-S premise.

Every point space has the independently constructed `schemePointTopology`.
The projective immersion supplies separatedness and finite affine
neighborhoods, so Y can be nonaffine. The actual S-integer extension is proved
finite projective. The actual completed-field tensor in
`SIntegerCompletedFieldTensor`, together with the finite-module topology of
each original upper completion, instantiates the general completed-tensor
Weil point comparison. The lower nontrivial complete norm is obtained from its
original discrete valuation. The counit identity states that each component
is the original relative Weil counit evaluated along the actual completed
factor test spectrum.

At a lower place outside S,
`curvePlacePrincipalSIntegerModelFieldPointHomeomorph_integralToField`
proves that extending coefficients from the original completed integer rings
to the completed fields commutes with the constructed field and integral
point homeomorphisms at every upper place. The proof is the original counit
naturality theorem applied to the original inclusions. The explicit scalar
towers make its coefficient square commute.

The integral-image equivalence proves that a field point of the actual lower
Weil model comes from an integral point exactly when each upper component
comes from an integral point of Y. The forward implication is the same
commuting square. For the reverse implication, choose integral preimages of
the upper components, use the inverse integral homeomorphism, and compare
field images using injectivity of the field homeomorphism. The integral image
is thus proved for actual point maps rather than assumed.

All fields share an arbitrary universe. The constants are finite, the lower
field has its original function-field presentation and is finite over the
specified parameter subfield, and the original upper extension is finite with
compatible constant-field structures. The denominator is nonzero. No
separability is required. The outside-S premise occurs only in the integral
compatibility and image clauses. Actual model existence is proved separately;
the finite-level adelic product and full adelic Weil comparison remain
obligations of the host task.
