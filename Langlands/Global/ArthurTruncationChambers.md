# Chamber identities for Arthur’s partial truncation

`Langlands.GroupScheme.ArthurRelative.tauHat_ne_zero_of_tau_ne_zero` compares the simple-root
and hatted cutoffs on the same interval of standard parabolics. The simple roots in the lower
index vanish on its level projection. The remaining simple roots in the upper index are
strictly positive when `tau` is nonzero. `ArthurCombinatorics.weightCoordinate_pos` makes each
required weight strictly positive on the projected vector. These weights agree on the input and
its projection because they vanish on the coroots removed by the projection.
[Cartan block and weight positivity](../LinearAlgebra/ArthurCombinatoricsSigma.md)

`Langlands.GroupScheme.ArthurRelative.sum_tauHat_mul_tau` is the relative version of Arthur’s
(8.11). It evaluates the alternating sum over intermediate parabolics as the indicator that its
endpoints agree. The proof specializes `ArthurCombinatorics.langlandsCombinatorial_eq` at the
zero functional. Every coroot value is then zero, so `phi` becomes `tauHat` and `epsilon` becomes
`(-1)` to the power of the cardinality of the index difference. The map `standardIndex` from
simple characters to the indices of the indivisible relative root system is bijective on the
interval, preserves cardinalities and gives the sign in the Library’s partial truncation.
[Langlands’ combinatorial lemma](../LinearAlgebra/ArthurCombinatoricsLanglandsLemma.md)

## Sources

- J. Arthur, *An introduction to the trace formula* (2005), (8.11), printed p. 46, PDF p. 58.
  Literature ID `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
  `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
- J. Arthur, *A trace formula for reductive groups I* (1978), §6 Lemma 6.3, printed pp. 940–941.
  Literature ID `arthur-1978-trace-formula-reductive-groups-I`, SHA-256
  `80ec482ea894e3af960e79cc1316ac2c2e806ad466f92c106650a59a0b2f17cc`.
