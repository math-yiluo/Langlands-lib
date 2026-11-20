# Comparing weak induction with weak base change to a full Galois orbit

`Langlands.Automorphic.Unramified.WeakInductionOrbitBaseChangeStatement.{uF,uE,uV,uW}`
says that if an actual cuspidal class `c` over `F` is weakly induced from
an actual cuspidal class `d` over a Galois extension `E`, the full Galois
orbit of `d`, with its multiplicities, is a weak base change of the singleton
datum of `c`. `CyclicOrbitBaseChangeWeakInductionStatement.{uF,uE,uV,uW}`
recovers weak induction from this weak base change if the extension is
cyclic and the actual lower class is fixed by the finite-order determinant
twist by a Hecke character `η` with exactly the norm kernel. Both directions
use spectral systems attached to the stated classes and data. They impose
no regularity condition on `d`.

The proof route is derived from Arthur and Clozel, *Simple Algebras, Base
Change, and the Advanced Theory of the Trace Formula* (1989), Chapter III,
§1 equation (1.1), printed p. 199, and Definition 6.1, §§6.1–6.2,
pp. 214–217. Their computation in (6.5)–(6.6) and the ensuing argument
relate the prime-degree base change and induced spectra in the presence of
the self-twist. In arbitrary degree the same calculation uses the
actual residue degrees. The forward implication is the restriction of
induction at unramified places, expressed on the supplied spectra.

At a base place `v` outside a finite set, all places above it have the
same residue degree `f`. At any one of them, the multiset of the spectra
of the conjugates of `d` is the union of the spectra of `d` at all places
above `v`, each taken `f` times. This uses attached Galois transport,
transitivity on places, and the order `f` of the decomposition group in
the unramified case. In weak induction, replacing each upper eigenvalue
`a` by the full set of roots of `X^f = a` gives exactly the induced Euler
polynomial. Taking `f`-th powers therefore recovers the multiset for the
full orbit. The rank follows from the degree equation for weak induction
and the formula for the rank of a Galois orbit.

For the converse, the actual self-twist and the determinant-twist spectral
transport make the lower spectrum invariant under multiplication by
`η_v(ϖ_v)`. The norm-kernel order statement makes this a primitive
`f`-th root of unity. Every nonzero eigenvalue then lies in a full orbit
of `f` roots of its `f`-th power, with multiplicity constant on that orbit.
Weak base change identifies the multiset of powers with the repeated
upper multiset. Cancel the `f` copies to recover each multiplicity in the
weak induction polynomial. Spectral comparison within a cuspidal class
and a common cofinite set allow independently supplied presentations
to be used. These are unramified identities and apply over totally complex
bases as well.
