# Normalized JPSS Euler polynomials under local-field isomorphisms

The theorem relates the actual `AllField` JPSS polynomial certificates over
two nonarchimedean local fields. The isomorphism is bicontinuous. The supplied
additive characters correspond by composition and the supplied additive Haar
measures by pushforward.

The isomorphism preserves the valuation rings, the residue cardinalities,
and the normalized absolute values. It therefore transports both normalized
group Haar measures. Existence of compatible quotient measures is preserved,
and each compatible measure is transported by the quotient homeomorphism.
At each such measure, `isPairLPolynomial_comp_iff` transports the common
polynomial of the zeta integrals. This gives the normalized certificate in
both directions. The same argument over canonical p-adic fields appears in
`FieldTransport.Padic`.
