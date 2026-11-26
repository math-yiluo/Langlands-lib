# Relative first étale cohomology and the character sheaf of torsion

Let \(\pi:A\to S\) be an abelian scheme and let \(n>0\) be invertible on
\(S\). The relative comparison in degree one is

\[
 R^1\pi_{\mathrm{et},*}\underline{\mathbb Z/n\mathbb Z}
 \ \cong\
 \underline{\operatorname{Hom}}_{\mathbb Z/n\mathbb Z}
 (A[n],\underline{\mathbb Z/n\mathbb Z}).
\]

`Langlands.Cohomology.AbelianFirstEtale.RelativeFirstEtaleCohomologyStatement`
asserts this isomorphism on the small étale site of \(S\). The base and
total schemes are in `Scheme.{0}`. The left side is the first actual
higher direct image of the constant sheaf valued in `ModuleCat.{0}` on
\(A\). The torsion sheaf on the right is obtained by sheafifying the
presheaf of sections of the multiplication kernel. At an étale test
object its internal Hom consists of linear natural transformations
between the two actual sheaves restricted to the slice. The Lean
definition equips these Hom types with their pointwise
\(\mathbb Z/n\mathbb Z\)-module structures and proves their sheaf condition.
The isomorphism is between presheaves valued in `ModuleCat.{1}`, with
the universe lift of the higher direct image matching the internal Hom.

For the mathematical comparison, the multiplication cover
\([n]:A\to A\) is a torsor under the pullback of \(A[n]\) to \(A\). Over
an étale test object \(U\to S\), push this torsor out along a character
of \(A[n]_U\) to get a class in \(H^1_{\mathrm{et}}(A_U,\mathbb Z/n\mathbb Z)\).
These classes commute with restriction and induce a morphism to the
higher direct image. Proper base change identifies its geometric stalks
with the cohomology of the geometric fibres. On an abelian variety over
an algebraically closed field, the degree-one torsor calculation
identifies this map with the character isomorphism for the multiplication
kernel at exponent \(n\). The invertibility hypothesis gives finite
étale multiplication kernels and permits use of the étale
degree-one torsor calculation. The proposition asserts the isomorphism
for a fixed exponent.

- J. S. Milne, *Étale Cohomology* (1980), III §4, Proposition 4.6 and
  Remark 4.8(a) for torsors and étale cohomology, and Corollaries 4.19(a)
  and 4.20 and their proofs, pp. 131–132, for the fibre calculation.
  Registered ID `milne-1980-etale-cohomology`, SHA-256
  `0a2f02682f82db8385e4dc6c77c7113900b11d6c313f34f8b354a3a9a391d232`.
- *SGA 4*, tome 3, Exposé XII, Corollary 5.2(iii), printed p. 89
  (PDF p. 92), for proper base change on the geometric stalks.
  Registered ID `sga4-1973-tome3-deligne-xvii-original-scan`, SHA-256
  `702fa23766ccec841d31ce0f21dfaacff8d8d31d4153de386587a27a4c01107a`.
- Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
  Varieties* (2001), III.2, printed p. 98 (PDF p. 106), uses \(R^1\pi_*\)
  and the dual standard Tate representation with rational adic
  coefficients. The statement here supplies the finite-stage relative
  comparison that enters that construction. Registered ID
  `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
