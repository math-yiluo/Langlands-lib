# The two unadjusted matrix operators on a p-adic field

`Langlands.Aubert.General.RationalPointFamily.GL.padicMatrixAlternatingOperatorSpecialization`
proves `PadicMatrixAlternatingOperatorSpecializationStatement.{u, v}`.
It applies to every prime `p`, p-adic field `F`, supplied topological datum
`T : F.TopologicalData` and natural rank `n`. Both operators act on the
same exact finite-length Grothendieck group of smooth complex
representations of \(\mathrm{GL}_n(F)\), with carriers in
`Type (max (u + 1) v)`. The local-field datum `T.toLocalFieldData`
uses `T.topology`.

For each ordered block shape `B`, `localFieldMatrixParabolicExactLength_padic`
takes the four preservation clauses from `padicMatrixFunctorSpecialization`.
They give preservation of finite length and of short exact sequences with
finite-length terms, for normalized induction and for normalized Jacquet
restriction.

`localFieldMatrixAlternatingOperator_eq_padic` takes any package of those
preservation witnesses. It unfolds `localFieldMatrixAlternatingOperator`
and uses `Aubert.alternatingOperator_eq_sum` to express both operators over
the same finite enumeration of block shapes. For each `B`, it passes the
four supplied witnesses to `padicMatrixFunctorSpecialization` to identify
the induction and Jacquet maps on exact classes with their p-adic
counterparts. Rewriting both maps identifies their composite, induction
after Jacquet, with the same coefficient \((-1)^{n-B.\mathrm{length}}\)
on both sides. `Finset.sum_congr` gives equality of the entire
\(\mathbb Z\)-linear endomorphisms. The argument includes the empty block
shape in rank zero, whose coefficient is \(1\).

The comparison is derived from the two matrix realizations of Aubert's
Definition 1.5 (printed p. 2181). In the GL setting of §2 (printed
pp. 2183–2184), a block shape with sizes \(b_1,\ldots,b_k\) has
\(\sum_i (b_i-1)=n-k\) simple roots inside its Levi, which gives the
coefficient used in the proof. Section 2 also takes \(G_0\) to be the
trivial group. The retained source `aubert-1995-duality` has SHA-256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`.
[Aubert (1995)](https://doi.org/10.1090/S0002-9947-1995-1285969-0)
