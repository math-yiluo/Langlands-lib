# Multiplication on the relative adic cohomology system

`Langlands.Cohomology.AbelianRelativeEtale.RelativeAdicMultiplicationCohomologyStatement`
states that pullback by the integer multiplication `[m]` on an abelian
scheme over `S` is the scalar `m^q` on the inverse system of relative
étale cohomology sheaves in degree `q`. The prime `p` is invertible on
`S`. At exponent `r`, the coefficient is the constant sheaf of
`ℤ_p/(p)^r`-modules viewed over `ℤ_p`. Coefficient reductions are the
actual quotient maps. Base and total schemes are in universe zero.
The two derived-category localizations are independent.

The diagram is the actual constant coefficient tower from
`EtaleAdicSystem.ellPowerConstantSystem`, followed by the ordinary higher
geometric direct image. `relativeAdicCohomologyPullback` uses the relative
pullback defined by the geometric derived unit, its composition
comparison, and the constant-sheaf inverse-image isomorphism. Naturality
of those maps in the coefficient module gives a morphism of the diagrams.
The asserted equality is in the functor category on the opposite of the
natural-number ordering, so it uses the same scalar at every exponent.

Milne, *Abelian Varieties*, §15, Theorem 15.1(a)–(b), printed pp. 27–28,
computes degree one on an algebraically closed fibre as the dual of the
Tate module and the higher groups as its exterior powers. Multiplication
acts on the Tate module by `m`, hence on the degree-`q` exterior power
by `m^q`. The integral groups are free. The natural reduction sequence
of Milne, *Étale Cohomology*, V.1, Lemma 1.11, printed pp. 165–166,
transfers the scalar to each prime-power coefficient stage. The proper
base change comparison on geometric stalks in SGA 4 XII,
Corollary 5.2(iii), printed p. 89, transfers the fibre computation to
the higher direct images over `S`. This stalk calculation uses the
constant module `ℤ_p/(p)^r`, so the scalar is computed in the same
coefficient category at each step. At `r = 0` the coefficient module is
zero. These are the degree weights used in the multiplication-by-two
part of the projector of Harris–Taylor III.2, printed p. 98.

| Edition | Registered ID | SHA-256 |
| --- | --- | --- |
| Milne, *Abelian Varieties*, author revision of 2 January 2022 | `milne-abelian-varieties-1986-author-2022` | `bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c` |
| Milne, *Étale Cohomology* (1980) | `milne-1980-etale-cohomology` | `0a2f02682f82db8385e4dc6c77c7113900b11d6c313f34f8b354a3a9a391d232` |
| SGA 4, tome 3 (1973) | `sga4-1973-tome3-deligne-xvii-original-scan` | `702fa23766ccec841d31ce0f21dfaacff8d8d31d4153de386587a27a4c01107a` |
| Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties* (2001) | `harris-taylor-2001-geometry-cohomology-simple-shimura` | `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b` |
