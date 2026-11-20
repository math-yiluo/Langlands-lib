# Twisting affine Nilp tests

Let \(R\) be a commutative \(O\)-algebra and let \(\sigma\) be an
\(O\)-algebra automorphism of \(R\) fixing the distinguished element
\(\pi\). `Nilp.twistFunctor` changes a structural map \(j:R\to A\)
to \(j\circ\sigma\). The ring \(A\) and the underlying ring maps of
test morphisms are the original ones. The image of \(\pi\) agrees
under both structures, so the new test again lies in `Nilp`.

The identity on \(A\) is \(O\)-linear, and the two \(\pi\)-reduction
ideals agree. The resulting equivalence on the actual quotients
sends each residue class to the class with the same representative.
Both equivalences are natural in the affine test and commute with
the quotient maps. On the residue coefficient ring the induced
automorphism sends \([r]\) to \([\sigma(r)]\). The final comparison
identifies the twisted residue structure with precomposition by
this induced automorphism.

This is the affine coefficient operation in Harris (1997), Appendix,
(A.4), printed p. 114 (PDF p. 40). His scheme structural map is
postcomposed with Frobenius, so the corresponding algebra structural
map is precomposed with the coefficient automorphism.
