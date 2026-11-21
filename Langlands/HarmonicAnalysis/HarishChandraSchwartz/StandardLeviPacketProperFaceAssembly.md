# Proper-face expansion data for the standard-Levi induction

`standardLeviPacketProperFaceExpansionAt_of_openFullDomains` proves
`StandardLeviPacketProperFaceAssemblyStatement`, constructing the input used
by `standardLeviPacketWeakBoundsAt_of_rankIH`. Its compact is the
common special compact, with the given ambient minimal-parabolic product.
The special-compact factorization first gives the literal minimal Iwasawa
pair in every standard Levi. `standardLeviDynamicIwasawaAt_of_minimal` then
gives the products for both actual opposite parabolics inside each output
Levi at that same intersection.

For each Weyl representative the proof builds its lower density package
through `exists_lowerDensityPackage_at_compact_of_openFullDomains`. At the
empty output face, `lowerPacketOpenFullDomains_of_emptyOutput` supplies the
full domains. Other proper faces use the stated convergence premise. The
exact weighted pointwise expansion is then specialized to the resulting
family of lower density packages. These packages have exactly the compact
normalization required by the rank induction.

This derived assembly supports the use of Waldspurger V.1.1 and VI.3.1, in
particular VI.3.1 at printed p. 304. It takes the exact pointwise identity
and the nontrivial lower convergence conditions as inputs, together with
the given common special compact. The upper and lower densities, the Borel
quotient Haar and the other inducing data have the types of the existing
weighted expansion.
