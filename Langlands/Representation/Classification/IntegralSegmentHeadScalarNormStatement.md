# Scalar norms of strong heads on an integral cuspidal line

`Langlands.Classification.IntegralSegmentHeadScalarNorm` is an internal
statement over every prime, supplied p-adic field `F` and topological datum
`T`, with independent field and representation universes and saturated
representation carriers.

For every positive-rank cuspidal datum `ρ`, there is one real number `t`
with the following property. If the actual segment `Δ` has inclusive integral
coordinates `[b,a]` on the twist line through `ρ`, every actual strong head
`π` of `Δ` has an actual scalar character `c` satisfying

\[
 \pi(z I)v=c(z)v,\qquad
 |c(z)|=|z|^{\deg(\Delta)(\,t+(a+b)/2\,)}.
\]

Here `|z|` is `T.normalizedAbs z`. The scalar action holds for every vector.
The parameter `t` is chosen before the interval, segment and head, so it is
common to any finite family on this cuspidal line. The character `c` is
existentially supplied for each actual head. The head is the Library's strong
increasing-product quotient, including uniqueness of the quotient kernel.

The proposed internal derivation chooses an actual supercuspidal
representative of `ρ`. Admissible Schur supplies its scalar character `ω`.
Smoothness and a nonzero vector make the scalar character's kernel open.
The Library's character real-part theorem then gives
`|ω(z)|=|z|^s`; take `t=s/ρ.rank`. Twisting this representative by the integer
`b` and applying the actual segment-constituent scalar-character theorem
gives the scalar character on `π`. Its exponent is

\[
 \ell s+\rho.\mathrm{rank}\,\ell
       \bigl(b+(\ell-1)/2\bigr)
 =\deg(\Delta)\bigl(t+(a+b)/2\bigr),
 \qquad a=b+\ell-1 .
\]

This pair defines the proposition and supplies no proof. It assumes neither
unitarity of the cuspidal representative nor freeness of its integral twist
orbit. It constructs no initial cuspidal word, segment head, induction
embedding, commutation isomorphism or classification theorem.
