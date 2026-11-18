# Radical filtration of a lattice-chain order

`Langlands.BushnellKutzko.radicalFiltration` proves all five clauses of
`Langlands.BushnellKutzko.RadicalFiltrationStatement`. It takes the field
and vector space in independent universes and constructs a uniformizer
and a finite splitting basis from the given lattice chain. The statement
records the identities on printed p. 21 and the bound needed for the
index in (1.1.3) on p. 22 of Bushnell and Kutzko, *The admissible dual of GL(N)
via compact open subgroups* (1993), §1.1. The source is registered as
`bushnell-kutzko-1993-admissible-dual-gln` and these are PDF pp. 33–34.

## Splitting basis and elementary maps

`IsDiscreteValuationRing.exists_irreducible` gives the uniformizer
\(\varpi\). `LatticeChain.exists_basis_splits` gives a basis \(\beta\)
whose coordinate projections preserve every lattice. This is the
decomposition along coordinate lines used in BK93 (1.1.7), printed
p. 23. Put \(\nu(w)=\texttt{LatticeChain.index}(w)\) for nonzero \(w\).
`LatticeChain.index_smul` gives
\(\nu(c w)=\nu(w)+e\,\operatorname{ord}_{\varpi}(c)\) for \(c\ne 0\).
Each strict inclusion \(L_{i+1}\subsetneq L_i\) gives a vector in the
difference. Its splitting basis expansion has a nonzero term \(c\beta_a\)
in the same difference, so \(\nu(c\beta_a)=i\) by
`LatticeChain.mem_iff_le_index`. This is `exists_scaled_basis_index`.
[Splitting basis](SplittingBasis.md)

`sum_elementaryEnd_entry` expands an endomorphism as the sum of
\(E_{kl}(t)\) over its matrix entries \(t\). For \(t\ne 0\),
`LatticeChain.elementaryEnd_mem_iff` says that \(E_{kl}(t)\) lies in
\(\mathfrak P^n\) exactly when its degree
\(e\,\operatorname{ord}_{\varpi}(t)+\nu(\beta_k)-\nu(\beta_l)\) is at
least \(n\). `LatticeChain.le_of_mem_endFiltration` gives the same bound
for every nonzero entry of an element of \(\mathfrak P^n\).
[Filtration coordinates](FiltrationCoordinates.md)

## The five clauses

1. The product inclusion follows from `Submodule.mul_le` and
   `LatticeChain.mul_mem_endFiltration`. For the reverse inclusion,
   expand \(x\in\mathfrak P^{m+n}\) into elementary maps. For each
   nonzero entry \(t\), choose \(c\beta_a\) of index
   \(\nu(\beta_l)+n\). Then \(E_{al}(c)\in\mathfrak P^n\) and
   \(E_{ka}(t c^{-1})\in\mathfrak P^m\) by the degree inequalities
   and `ordOf_mul` and `ordOf_inv`. `elementaryEnd_mul` identifies
   the product \(E_{ka}(t c^{-1})E_{al}(c)\) with \(E_{kl}(t)\).
   `Submodule.mul_mem_mul` puts it in the product submodule, which
   also contains zero entries and the sum.

2. Each \(x\in\mathfrak P^n\) sends \(L_i\) into \(L_{i+n}\) by
   definition, giving the span inclusion via `Submodule.span_le`.
   For a vector of \(L_{i+n}\), split it into terms \(t\beta_k\)
   and fix \(c\beta_a\) of index \(i\). Each nonzero term is
   \(E_{ka}(t c^{-1})(c\beta_a)\), with the elementary map in
   \(\mathfrak P^n\) by the same degree inequality. These images
   lie in the span by `Submodule.subset_span`.

3. `LatticeChain.uniformizer_smul_mem_iff` applied to \(xv\) shows
   \(\varpi x\in\mathfrak P^{n+e}\) exactly when
   \(x\in\mathfrak P^n\). Multiplication by \(\varpi^{-1}\) supplies
   a scalar preimage for every element of the shifted step.
   `Irreducible.maximalIdeal_eq`, `Submodule.ideal_span_singleton_smul`
   and `LatticeChain.toSubmodule_order` then give the equality at
   \(n=0\).

4. For \(x\in\mathfrak P^1\) and \(y\) in the order,
   `LatticeChain.mul_mem_endFiltration` puts \(yx\) in
   \(\mathfrak P^1\). `LatticeChain.exists_mem_unitFiltration` gives
   an inverse of \(1+yx\) in the order. The inverse satisfies the
   left-inverse equation required by `Ideal.mem_jacobson_iff` at
   the zero ideal, using `Ideal.jacobson_bot`. Conversely, if a
   radical element \(x\) fails to belong to \(\mathfrak P^1\), its
   expansion has an elementary summand \(E_{kl}(t)\) outside
   \(\mathfrak P^1\). Its nonzero coefficient has degree at most
   zero, so \(y=E_{lk}(t^{-1})\) has nonnegative degree and lies in
   the order. The composition \(yx\) fixes \(\beta_l\). The
   radical criterion at \(-y\) gives \(z(-y)x+z-1=0\) for some
   \(z\) in the order. Evaluating on \(\beta_l\) gives
   \(-\beta_l=0\), contradicting that it is a basis vector.

5. `Finite.bddBelow_range` bounds the finitely many entry degrees
   from below. At any such lower bound every nonzero elementary
   summand belongs to the corresponding step, as do the zero
   summands, giving nonemptiness. A nonzero endomorphism has a
   nonzero matrix entry by the double sum formula. Its degree is
   an upper bound by `LatticeChain.le_of_mem_endFiltration`.

## Published Library inputs

- `Langlands.BushnellKutzko.RadicalFiltrationStatement` is the exact
  target proposition. [Target statement](RadicalFiltrationStatement.md)
- `Langlands.BushnellKutzko.LatticeChain` supplies `lattice`,
  `isLattice`, `lattice_succ_lt`, `exists_period`, `antitone`,
  `period`, `period_pos`, `lattice_add_period`, `endFiltration`,
  `mul_mem_endFiltration`, `order` and `toSubmodule_order` in the
  `LatticeChain` namespace, together with
  `jacobson_integer_eq_maximalIdeal`. [Lattice chains](LatticeChain.md)
- `Langlands.BushnellKutzko.UnitFiltration` supplies
  `LatticeChain.unitFiltration` and
  `LatticeChain.exists_mem_unitFiltration`.
  [Unit filtration](UnitFiltration.md)
