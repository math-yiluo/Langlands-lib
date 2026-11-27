# The support-adjusted graded Aubert operator over a local field

`Langlands.Aubert.LocalFieldGraded.gradedAdjustedOperator` applies
`adjustOperator` to the actual alternating induction–Jacquet operator in
each rank and takes the direct sum of the resulting linear maps. Its
inputs give finite-length and exactness preservation for the actual
matrix functors, as required to form the unadjusted operator on exact
Grothendieck groups. The homogeneous formula restricts the graded map to
the corresponding operator on every rank summand. On an actual
irreducible class with \(k\) cuspidal support factors in rank \(n\), the
value is the unadjusted value multiplied by \((-1)^{n-k}\).

The construction combines the alternating operator of Aubert
Definition 1.5 with the sign of Definition 2.1. The direct sum is over
all natural ranks, including the trivial rank-zero group specified at
the start of §2.

- `aubert-1995-duality`, SHA-256
  `57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`,
  Definition 1.5, printed p. 2181, and §2, printed pp. 2183–2184.
