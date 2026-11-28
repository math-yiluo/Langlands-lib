# Supercuspidal support of a σ-orbit product

Let `E` be a finite extension of `ℚ_p` with supplied topological data `T`.
Let `F` be a field equipped with a topology and an algebra structure on
`E`. Take an `F`-algebra automorphism `σ` of `E` and assume that `T` gives
`E` its `F`-module topology (`IsModuleTopology F E.Carrier`).
`SigmaOrbitProductSupportStatement` says that the ordinary supercuspidal
support of an irreducible unitarizable smooth complex seed on `GL_m(E)`
occurs with its multiplicities in the support of its normalized `σ`-orbit
product. For positive orbit length `t` and rank `m`, the product may
be given by an equivalent smooth complex representation on `GL_n(E)`
via `t * m = n`. The input carrier universe is independent of the field
universes. The support comparison uses the maximum of the `E` and
carrier universes.

The orbit product is the normalized induction of the powers of σ applied to
the seed, as in Henniart–Lemaire (2011), §II.4.12, printed p. 96.
Zelevinsky (1980), §1.10, printed p. 174, characterizes ordinary
supercuspidal support by constituents of normalized cuspidal induction
and proves its uniqueness. The Library's
`normalizedUnitaryProduct_hasSupercuspidalSupport` computes the support
of the irreducible normalized unitary product as the multiset sum of the
supports of its factors.

The Lean proof lifts the carriers to the universe used by the support
formula and compares the normalized inductions through the equivalences of
their factors. Each pullback factor stays smooth, irreducible and
unitarizable. Supercuspidal embedding supplies its support. At index zero
the entrywise automorphism is the identity, so uniqueness of support
identifies this summand with the supplied seed support. The submultiset
inclusion follows by taking the sum of the supports of all the factors.
