# The given and norm-defined presentations of local-field integers

This internal construction transports actual integral models from the integer
subring of the canonical norm to the given valuation integer subring of a
nonarchimedean local field F. It works at arbitrary universe `u` and retains
the actual generic group G over F.

`givenIntegerModel` uses the published equality `localNormedField_integer` of
these subrings. The private generic construction transports an integral model
across equality of subrings of the same fraction field. Substitution of that
equality, with fraction-field witnesses identified by proof irrelevance,
retains the supplied generic identification. `givenIntegerModel_smooth`
transports smoothness through the same equality.

`givenIntegerModel_unramified_eq` proves literal equality of the full actual
unramified coefficient model after this presentation transport with the
coefficient extension of the original norm-integer model. This includes the
generic identification. The coefficient algebra on norm integers is the
given integer-to-fixed-field map precomposed with the same-element subring
equivalence; its map to the inertia field is the original field inclusion.
The relevant scalar towers are proved. The generic equality argument for
subrings compares the two coefficient algebra structures on elements with
the same fraction-field value, then substitutes their equality. Thus the
comparison retains the exact original coefficient maps, rather than just an
unspecified abstract ring equivalence.

`givenIntegerModelIso` transports any supplied compatible upstairs model
isomorphism across that full coefficient-model equality, retaining its
prescribed generic map. In particular a generic-identity model comparison
remains a generic-identity comparison over the given valuation integers.

This is an internal consequence of the published same-subring identity and
actual model/coefficient definitions. It constructs no norm-integer model,
upstairs comparison or arithmetic extension theorem; these are inputs or
independent obligations. It is a presentation comparison, not a proof of KP
Fact 2.10.16.
