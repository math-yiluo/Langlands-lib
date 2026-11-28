# Compatible Iwasawa integration for a change of compact subgroup

Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein
series* (2011), §2, p. 311, chooses Iwasawa-compatible measures and defines
the inducing norm by quotient integration. The retained volume PDF
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`, page 320, has
SHA-256 `760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`.

`principalParabolic` is the intersection of the ambient rational subgroup
with the adelic parabolic image. `quotientIwasawa` applies
`ParabolicIwasawaMeasure.unfoldDiscreteIwasawa` to its counting-normalized
quotient. For a continuous left `U(𝔸) M(F)`-invariant integrand, the radical
coordinate drops out because its quotient measure has mass one. The
principal Levi coordinate descends to `M(F) \ M(𝔸)`, with inverse modulus
and the given compatible Haar measure. `quotient_weightedProduct` applies
this calculation to the product of the two forms with a height weight.
It yields an integrability equivalence and identifies `inducedInnerProduct`
with the integral on the discrete parabolic quotient for integrable data.

`inducedInnerProduct_shift` translates a real height weight by a vector in
its coordinates. Those coordinates are attained by a positive point of
the central split component of the Levi. Right translation by that point
preserves the rational Levi quotient measure. The two half moduli from
the forms cancel the change in the inverse modulus, giving the weight
shift identity.

`integrable_normWeight_of_integrable_kernel` goes from an integrable diagonal
weighted kernel with a nonzero compactly supported weight to the defining
square-integrability condition on the canonical Levi quotient. It uses
`exists_lintegral_rationalQuotient_kernel` to factor the inner absolute
integral by a finite scalar. For a nonzero form, the scalar is nonzero
because a nonzero weight is attained at a central split coordinate and
the continuous diagonal kernel is nonzero at a suitable translate. The
rational quotient measure charges nonempty open sets. Fubini then gives
the finite unweighted square integral on the canonical Levi quotient.
