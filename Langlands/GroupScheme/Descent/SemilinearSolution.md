# Semilinear recovery of an actual descent solution

This internal result extracts the semilinear transport law of an actual
solution from a component of its Čech datum. The base, cover and group schemes
are arbitrary in universe `u`; finiteness and field hypotheses are unnecessary.

`Solution.semilinearIso` constructs an actual isomorphism `a*H ≅ H` by
transporting the canonical semilinear comparison on the descended object
through the solution's isomorphism. Its inputs are a solution and an
endomorphism `a` of the cover satisfying `a ≫ p = p`.

`Solution.semilinear` assumes a component of the overlap with first projection
the identity and second projection `a`, together with the equality identifying
the datum on that component as the normalized transport of an isomorphism
`e : a*H ≅ H`. It pulls the solution's actual compatibility equation to that
component. The published canonical-component comparison and naturality of the
identity pullback reduce this equation to the claimed semilinear law by
cancelling isomorphisms.

`Solution.semilinearIso_eq` cancels the base change of the solution's
isomorphism in that law, showing that the constructed isomorphism is
exactly the supplied normalized component.

The result is derived from the published actual datum and pullback APIs. It
does not construct a component, a datum or a semilinear isomorphism from point
stability. Its use in unramified model descent still requires those inputs.
