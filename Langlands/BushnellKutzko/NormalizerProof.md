# The normalizer of a lattice chain

`Langlands.BushnellKutzko.normalizer` proves
`Langlands.BushnellKutzko.NormalizerStatement.{u, v}` with independent universes for the
field and vector space. Write \(O=\mathcal O_F\), \(A=\operatorname{End}_F(V)\) and \(G=A^\times\).
For \(\mathcal L=(L_i)\), `LatticeChain.lattice` gives \(L_i\). The proof uses `LatticeChain.order`,
`LatticeChain.endFiltration`, `LatticeChain.unitFiltration` and `LatticeChain.stabilizer` for
\(\mathfrak A\), \(P^n\), \(U^n\) and \(\mathfrak K\), respectively. Here \(P^n\) is the
integer-indexed filtration defined by lattice shifts.

The statement comes from Bushnell and Kutzko, *The admissible dual of GL(N) via compact open
subgroups* (1993), §1.1, printed pp. 20–22 (PDF pp. 32–34,
`bushnell-kutzko-1993-admissible-dual-gln`). For the depth-zero unit normalizer, they refer to
Bushnell and Fröhlich, *Non-abelian congruence Gauss sums and p-adic simple algebras* (1985),
the proof of (1.3.10), printed p. 220 (PDF p. 14,
`bushnell-frohlich-1985-nonabelian-congruence-gauss-sums`). The Lean proof derives the converse
normalizer inclusions by evaluating endomorphisms and units on individual vectors.

## Evaluation on a lattice layer

`exists_layer` puts every nonzero \(z\) in a successive difference \(L_i\setminus L_{i+1}\).
Using `LatticeChain.isLattice` and `Submodule.IsLattice.span_eq_top`, it clears denominators
in the \(F\)-span of \(L_0\) with `multiple_mem_span_of_mem_localization_span`. It factors
the nonzero denominator as a unit times a power of a uniformizer with
`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`. Periodicity then puts \(z\) in
some \(L_{-ke}\). If the indices containing \(z\) were unbounded above,
`LatticeChain.antitone` would put \(z\) in every \(L_{ke}=\mathfrak p_F^k L_0\).
`Ideal.iInf_pow_smul_eq_bot_of_isLocalRing` rules this out in the finite \(O\)-module \(L_0\).
`Int.csSup_mem` supplies the greatest index containing \(z\). Conversely, each successive
difference has a vector by `LatticeChain.lattice_succ_lt`.

If \(z\in L_i\setminus L_{i+1}\), its image modulo \(\mathfrak p_F L_{i+1-e}\) is nonzero.
`exists_integral_functional` chooses an \(O\)-basis of \(L_{i+1-e}\) with
`Module.Free.chooseBasis` and finds a unit coordinate of \(z\) in that basis.
`Module.Basis.extendOfIsLattice` extends the basis to an \(F\)-basis of \(V\).
The corresponding coordinate functional takes integral values on \(L_{i+1-e}\).
`exists_layer_functional` rescales it by the inverse unit to obtain \(f(z)=1\).
The identifications with \(\mathfrak p_F L_{i+1-e}\) and the corresponding
uniformizer-scaled lattices use `LatticeChain.period`, `LatticeChain.period_pos`,
`LatticeChain.lattice_add_period`, `Langlands.BushnellKutzko.jacobson_integer_eq_maximalIdeal`
and `IsDiscreteValuationRing.irreducible_iff_uniformizer`.

For \(w\in L_{i+n}\), `rank_one_mem_filtration` shows that \(y\mapsto f(y)w\) lies in
\(P^n\). For \(i+1-e\le j\le i\), integrality of \(f\) on \(L_j\) and the inclusion
\(L_{i+n}\subseteq L_{j+n}\) give the required mapping property. Periodicity and cancellation
of the nonzero uniformizer transport this property to every \(j\in\mathbb Z\).
Since the rank-one map sends \(z\) to \(w\), `eval_filtration` obtains \(P^n z=L_{i+n}\)
as sets. The other inclusion follows from `LatticeChain.mem_endFiltration`.

## From conjugation to stabilization

`conjugate` uses `LinearEquiv.conjRingEquiv` to implement \(x\mapsto gxg^{-1}\).
If this ring equivalence preserves \(P^n\) as a set, `image_eval_conjugate` gives
\(g(P^n z)=P^n(gz)\). To recover the image of \(L_k\), choose \(z\) in layer \(k-n\).
The nonzero vector \(gz\) lies in some layer \(j\), so the evaluation identity gives
\(gL_k=L_{j+n}\). This is `LatticeChain.mem_stabilizer`. Depth zero gives the
converse for the order via `LatticeChain.mem_order_iff_mem_endFiltration`.

At positive depth, `LatticeChain.exists_mem_unitFiltration` supplies the unit
\(1+x\) for \(x\in P^n\). For a normalizer element \(g\), its conjugate is in \(U^n\)
by `Subgroup.mem_normalizer_iff`. Subtracting \(1\) gives \(gxg^{-1}\in P^n\)
by `LatticeChain.mem_unitFiltration`. Applying the inclusion to both \(g\) and
\(g^{-1}\) gives preservation of \(P^n\) as a set, so the preceding evaluation
argument applies.

At depth zero, `span_eval_units` recovers \(L_i\) as the \(O\)-span of the \(U^0\)-orbit
of a layer vector \(z\). The orbit lies in \(L_i\) by `LatticeChain.mem_unitFiltration_zero`
and `LatticeChain.mem_order`. For \(y\in L_i\), the integral functional gives
\(y=cz+w\) with \(c=f(y)\in O\), \(w\in L_i\) and \(f(w)=0\). The rank-one map
\(x=f(\mathord{-})w\) is in \(P^0\) and squares to zero. Thus \(1+x\), with inverse
\(1-x\), is in \(U^0\) and sends \(z\) to \(z+w\). The orbit span contains both
\(z+w\) and \(z\), hence \(y\). `Subgroup.mem_normalizer_iff_conj_image_eq` and
`Submodule.map_span` show that a normalizer element carries this orbit span to the
corresponding span for \(gz\). This again verifies `LatticeChain.mem_stabilizer`.

## Normalization, valuation and translates

Every \(u\in U^n\) preserves each \(L_i\) as a set because both \(u\) and \(u^{-1}\)
belong to the order. For \(g\in\mathfrak K\), let \(d\) be `LatticeChain.stabilizerValuation g`.
`LatticeChain.map_lattice_stabilizer` gives \(gL_i=L_{i+d}\). Applying this equality
at \(i-d\) gives the needed preimages for \(g^{-1}\). Hence \(g\in P^d\) and
\(g^{-1}\in P^{-d}\). `LatticeChain.mul_mem_endFiltration` puts \(gxg^{-1}\) in
\(P^{d+n-d}=P^n\) for \(x\in P^n\). With the same argument for \(g^{-1}\), this
gives order normalization at \(n=0\) and unit group normalization by the three
conditions in `LatticeChain.mem_unitFiltration`, applied to \(u\), \(u^{-1}\) and \(u-1\).
The two normalizer inclusions give equality at every depth.
`Subgroup.normal_subgroupOf_iff_le_normalizer` gives normality inside \(\mathfrak K\).

If \(g\in P^n\), then \(L_d=gL_0\subseteq L_n\), so \(n\le d\) by
`LatticeChain.strictAnti`. The depth \(d\) is attained, and \(g\) is nonzero
because it carries a layer vector to a nonzero vector. `LatticeChain.valuation`
therefore evaluates to \(d\) by `IsGreatest.csSup_eq`. Multiplication by
\(g\in P^d\) on either side takes \(\mathfrak A=P^0\) into \(P^d\).
For \(x\in P^d\), both \(g^{-1}x\) and \(xg^{-1}\) lie in \(P^0\) by
`LatticeChain.mul_mem_endFiltration`, giving the required preimages for the two translates.
