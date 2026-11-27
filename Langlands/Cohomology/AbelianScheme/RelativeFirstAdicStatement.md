# Compatibility of the relative first cohomology character isomorphisms

Let \(A\to S\) be an abelian scheme and let \(p\) be a prime invertible
on \(S\). At each exponent \(r\), write \(C_r\) for the constant sheaf
with module \(\mathbb Z_p/(p)^r\). The relative first-cohomology
comparison identifies \(R^1\pi_* C_r\) with the sheaf of characters
from \(A[p^r]\) to \(C_r\). Both are viewed over \(\mathbb Z_p\).

`RelativeFirstAdicCharacterCompatibilityStatement` asserts that these
isomorphisms can be chosen so that for \(r\le s\) and a local cohomology
section \(x\) at exponent \(s\),
\[
    \operatorname{red}_{s,r}\circ\chi_s(x)
       = \chi_r(\operatorname{red}_{s,r} x)\circ [p^{s-r}].
\]
The equality is between maps on the étale slice over each test object.
The left side uses coefficient reduction, and the right side
precomposes with the torsion map from \(A[p^s]\) to \(A[p^r]\).
The cohomology is the actual `relativeAdicCohomologySystem` in degree
one. The torsion sheaf is the sheafification of the sections of the
group-scheme multiplication kernel with the residue scalar action.
Its transition sheafifies `Langlands.GroupScheme.Tate.transition`,
which is multiplication by the quotient of the two orders. The
internal Hom uses linear maps of the restricted sheaves and has the
sheaf condition. The schemes are in universe zero and the character
presheaf is valued in the next module universe, using the same
universe lift on the cohomology side as in the fixed-exponent
comparison.

For the source calculation, push the multiplication torsor
\([p^s]:A\to A\) out along a character and then reduce coefficients.
The map of multiplication torsors induced by \([p^{s-r}]\) lies over
the identity and induces the displayed torsion map. Pushing out in
these two orders gives the same torsor class. This calculation works
over each étale test scheme. Proper base change and the fibrewise
character calculation identify the degree-one relative maps as
isomorphisms. This gives the simultaneous finite-stage statement used
in passing to the adic coefficients in the geometric realization.

- Milne, *Étale Cohomology* (1980), III.4 Proposition 4.6 and Remark
  4.8(a) for the torsor interpretation and coefficient maps, and
  Corollaries 4.19(a) and 4.20, printed pp. 131–132, for the character
  calculation. Chapter V.1, printed p. 164, defines the cohomology of
  the adic system. Registered ID `milne-1980-etale-cohomology`, SHA-256
  `0a2f02682f82db8385e4dc6c77c7113900b11d6c313f34f8b354a3a9a391d232`.
- *SGA 4*, tome 3, XII.5 Corollary 5.2(iii), printed p. 89, for the
  proper base change comparison. Registered ID
  `sga4-1973-tome3-deligne-xvii-original-scan`, SHA-256
  `702fa23766ccec841d31ce0f21dfaacff8d8d31d4153de386587a27a4c01107a`.
- Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
  Varieties* (2001), III.2, printed p. 98 (PDF p. 106), for the relative
  adic sheaf and the dual of the standard Tate representation. Registered
  ID `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
