# Descent through actual ideal quotients

This internal module develops the universal property of the actual quotient
`IdealAdic.quotient f I M`. For a map `φ : M → N`, vanishing on the sheaf
of ideal multiples is equivalent to the assertion that, on every open `U`,
`φ` sends every product `scalar f U a • m`, for `a ∈ I`, to zero.

The proof uses the sheafification adjunction to identify the composite out
of the ideal-multiple sheaf with the presheaf composite out of the local
span. A linear map vanishes on that span exactly when it vanishes on all
its generators. No geometric or finiteness assumptions are needed.

`desc` is the resulting canonical map from the quotient. `projection_desc`
proves its compatibility with the original map, and `desc_unique` proves
uniqueness by cancellation of the epimorphic quotient projection.
These are derived universal-property constructions for `IdealAdicQuotients`;
no identification with a geometric closed fibre or lifting claim is made.
