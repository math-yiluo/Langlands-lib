# Isomorphisms on full-centre fppf quotients over arbitrary bases

This internal development extends the published field-only adjoint quotient
isomorphism construction to any base scheme and any supplied fppf quotient by
the full centre. The hypotheses are flatness, surjectivity, local finite
presentation, and equality of the kernel range functor with the full centre.

The homomorphism descends by `CenterQuotientDescent.overHom`. The identity and
multiplication laws descend by epimorphy of the quotient map and its product.
Transport of central points by an ambient isomorphism supplies the factorization
in each direction; epimorphy proves that these descended maps are inverse and
that the quotient square determines the result uniquely.

For a natural local isomorphism over any `U`, recover the actual base-change
isomorphism, apply the quotient construction after base change, then return to
local values. `localIso_square` follows from the actual base-change square.
No quasi-compactness, field, reductivity, or closedness assumption is added.
This is a derived construction, not a proof of the semi-local quasi-split
inner-form theorem.
