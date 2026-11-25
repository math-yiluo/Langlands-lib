# Lying over for finite Banach maps over arbitrary valued fields

This derived helper extends the proof route of `StrictTestDomain.LyingOver` to
`IsFiniteBanach`, without assuming a nontrivial valuation. Norm-controlled
finite coefficients bound every ring map that is contractive on the base.
For a spectrum point killing the kernel, algebraic lying over supplies a prime
of the finite target above its kernel. Embed its residue algebra into an
algebraic closure of a complete isometric extension of the completed residue
field. The extension realizes radius 2 and is therefore nontrivially normed,
so Mathlib's spectral norm equips the algebraic closure with the required norm.
The coefficient estimate bounds the constructed ring map. Pulling back that
norm gives the desired bounded spectrum point.

This is the finite-map surjectivity input used in the derived proof of the
étale specialization of Berkovich (1993), Proposition 3.2.7, printed p.59.
It needs neither completeness of the two normed algebras nor nontriviality of
the coefficient norm; finiteness is the existing norm-controlled
`BoundedAlgHom.IsFiniteBanach` predicate.
