# Actual polarized automorphisms and the Rosati norm

This is an internal algebraic bridge between the existing definitions of actual
integral polarized automorphisms and the actual Rosati construction. It does not
assert unconditional finiteness or positivity.

For the existing Rosati prerequisites `P`, dual witnesses `W`, additivity witness,
and a dual-valued map `lam` that is invertible in the rational category, the
polarization-preserving equation implies that the Rosati conjugate of the
canonical rational homomorphism is its rational inverse. Both products are
therefore the identity. No polarization or positivity assumption is needed for
these algebraic conclusions beyond the explicit preservation equation and
rational invertibility.

`integralTraceForm` restricts the existing actual rational Rosati trace form along
`homToHom0` in both arguments and restricts scalars to the integers. The diagonal
value on every actual polarized automorphism is the geometric trace of the
identity. This is an equality; no trace comparison or dimension formula is used.

The norm proof rationalizes the existing integral preservation equation, composes
with the actual inverse of `lam`, and reassociates. Uniqueness of the categorical
inverse identifies the conjugate with the automorphism's inverse, giving the
other product identity and then the trace-form equality.

`homToHom0_injective_of_charZero` uses the published integral reflection theorem.
Every positive integer is a unit over the characteristic-zero base field, and
the global-sections isomorphism of its spectrum transports these units to the
required ring of global functions. The result concerns the canonical
rationalization of actual integral Hom groups.
`polarizedAutRationalization_injective` then projects an equality of the actual
rationalized automorphisms to their homomorphisms, applies this injectivity, and
uses extensionality of isomorphisms and subgroup elements.
