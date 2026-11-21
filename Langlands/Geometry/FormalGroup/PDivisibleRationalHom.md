# Rational morphisms of actual p-divisible groups

`Langlands.PDivisibleGroup.RationalHom G H` is
\(\mathbb Q_p\otimes_{\mathbb Z_p}\operatorname{Hom}(G,H)\), where an integral
morphism is a compatible map of the actual finite group schemes. The map
`ofHom` inserts coefficient one. `comp` extends composition by tensor
bilinearity and multiplies the field coefficients. The identity is the
image of the integral identity. These operations make `RationalCategory`
a \(\mathbb Q_p\)-linear category. `QuasiIsogeny` is an isomorphism in this
category.

`exists_pPower_ofHom` clears denominators in the tensor. The localization
of the module of integral morphisms gives a single nonzero coefficient in
\(\mathbb Z_p\) that clears a given tensor. Write this coefficient as a unit
times a power of \(p\), then absorb the inverse unit in the integral
morphism.

Harris describes quasi-isogenies as sections of rationalized Hom that
locally admit an isogeny numerator. This construction gives the global
tensor and its composition on the affine base, and the denominator lemma
gives an integral numerator. The isogeny property of a numerator belongs
to the comparison with the finite kernels of the actual towers. See Harris (1997), Appendix, printed p. 112 (PDF p. 38),
the paragraph defining quasi-isogenies.
