# Prime cyclic realization of a regular orbit by a cuspidal class

`Langlands.Automorphic.Unramified.CyclicPrimeRegularOrbitRealizationStatement`
and `CyclicPrimeRegularOrbitRealizationTCStatement` isolate the cuspidal
existence clause of Arthur–Clozel, *Simple Algebras, Base Change, and the
Advanced Theory of the Trace Formula* (1989), III.4.2(e), printed p. 202
(PDF p. 216). The proof occupies printed pp. 207–210 (PDF pp. 221–224).
Registered source `arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.

The inputs are an actual cuspidal realization `T` of rank `m + 1` over `E`,
with unitary central character, a prime-degree cyclic extension `E/F` of
number fields and a generator `σ` with `T` inequivalent to its conjugate by
`σ`. In prime degree this gives a distinct class for every automorphism.
`IsobaricData.galoisOrbit` takes one copy of each of these classes with the
published pullback convention. The output is an actual cuspidal realization
`S` over `F` with unitary central character and rank `(m + 1)[E : F]`. A
weak base-change witness uses genuine attached spectral systems for the
singleton of `S` and the full orbit of `T`. The identity holds at all places
above almost every base place, with the actual residue-degree power, as in
III.1.1. The two field universes and the two spectral-presentation universes
are independent.

III.4.2(e) derives occurrence from the identity of the discrete expressions
(4.1) and (4.2), which specialize II.(17.8). On the twisted side the block
Levi of type `(m + 1, …, m + 1)` has an orbit contribution from the Coxeter
permutation. The normalization (4.3), the composition relation (4.4) and
Galois equivariance identify the contributions of the reordered supports.
Hecke character separation then gives an automorphic constituent on the
untwisted side. The source uses lower-rank lifting and the poles of the
Rankin–Selberg products in (4.5) to prove cuspidality. The existence clause
here includes that last step. Automorphic induction, determinant self-twist,
and uniqueness of the lift are separate conclusions of the surrounding
source and are outside the scope of these propositions.

The TC proposition imposes total complexness on `F`. Every infinite place
then splits completely in `E`. The trace comparison uses split matching at
those places and the needed cyclic test-function matching at finite places.
The regular orbit argument requires the contribution of a proper Levi in the
discrete expression. The prime realization is therefore a target for the
discrete trace identity and extraction argument, beyond the simple trace
identity for tests with split supercuspidal places. The TC proposition can be
proved by restricting that analytic argument to totally complex fields. Its
conclusion is the same weak finite-place relation.
