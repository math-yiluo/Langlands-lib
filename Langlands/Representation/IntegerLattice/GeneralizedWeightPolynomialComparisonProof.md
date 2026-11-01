# The particular block polynomials give the actual action and coefficients

Worker 88 proves the unchanged Library proposition
`Langlands.RenardCIIIPolynomialComparisonStatement.{u}` in the theorem
`Langlands.renardCIIIPolynomialComparison.{u}`. Its three components identify
the particular published polynomial matrices with the actual restricted
lattice action, contract them to the actual coefficient in every compatible
basis pair, and supply simultaneous compatible witnesses.

## Source and derived provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix C.III, printed
pp.279–280 / one-based PDF285–286. The registered identifier is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Both pages were read directly, and the product on PDF286 was also checked
visually. Renard normalizes each generator on a simultaneous block, expands
its integer power by a finite binomial formula, and obtains polynomial
entries and general coefficients by linearity.

The supplementary older-edition corrections,
`renard-2010-corrections-complements`, PDF18–19, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were also read directly. They correct the grouping of the whole
scalar-times-unipotent factor under each integer power; the 2026 formula
already has that grouping. The imported product theorem uses genuine
integer powers of units and retains negative coordinates.

The named polynomial witnesses, ordered scalar-polynomial matrix product,
uniform ambient-finrank cutoff, explicit basis compatibility and three
closed comparison propositions are derived formulations of that passage.
This proof imports their published constructions and statement unchanged.
It uses the published actual-block product, decomposition and global-basis
theorems; it does not use the existential coefficient theorem as a
comparison for the particular polynomials.

## Polynomial evaluation and the actual restricted action

Write `W_c = generalizedWeightBlock A c`, `r_c = finrank ℂ W_c`,
`D = finrank ℂ V` and `N_i = normalizedGeneratorDifference A c i`.
For each supplied local basis `b : Basis (Fin r_c) ℂ W_c`, the helper
`IntegerLattice.PolynomialComparison.eval_matrix` proves at every complex
point x that evaluating the particular polynomial matrix gives the matrix
of the ordered endomorphism product

```text
(List.ofFn (fun i => ∑ k ∈ Finset.range D, Ring.choose (x i) k • N_i ^ k)).prod.
```

For a single factor, the proof uses the published entrywise evaluation
lemma and the algebra equivalence `LinearMap.toMatrixAlgEquiv b` to move
the sum and scalar actions through the matrix map. It then uses preservation
of list products by both maps. The order of factors and the cutoff D are
preserved; no commutativity of the endomorphism ring is assumed.

`commutingTupleGeneralizedWeightPolynomialAction` applies the third clause
of `commutingTupleGeneralizedWeightProduct` at the actual lattice point n.
It transports that endomorphism equality through the same matrix algebra
equivalence, uses `eval_matrix` at `x i = (n.toAdd i : ℂ)`, and reads off
each row p and column q. This proves exactly

```text
b.repr (generalizedWeightBlockRepresentation A c n (b q)) p
  = (coordinateCharacter c n : ℂ) *
      eval x (generalizedWeightPolynomialMatrix A c b p q).
```

The supplied basis is arbitrary; the argument needs no triangularity.

## Finite reconstruction and coefficient contraction

`IntegerLattice.PolynomialComparison.sum_block_coordinates` takes an
ambient sigma-indexed basis B and a finite set s with
`c ∈ s ↔ W_c ≠ ⊥`. It proves

```text
∑ c ∈ s, ∑ q : Fin r_c, B.repr v ⟨c,q⟩ • B ⟨c,q⟩ = v.
```

Any index `q : Fin r_c` gives `0 < r_c`; if `W_c = ⊥`, its finrank
would be zero. Thus every such c lies in s. The finite sigma finset over s
therefore contains the finitely supported coordinates `B.repr v`.
Extending that support to this finset, using zero coordinates outside the
support, and applying `B.linearCombination_repr` proves the formula.
`Finset.sum_sigma` writes it as the displayed double sum. No `Fintype`
instance for the whole label type or its full sigma type is introduced.

`IntegerLattice.PolynomialComparison.functional_block_action` reconstructs
the restricted action on a local basis vector with `b.sum_repr`, applies
the algebraic complex-linear functional ell after inclusion in V, and
replaces every coordinate by the proved polynomial-action identity.

`commutingTupleGeneralizedWeightPolynomialCoefficient` first obtains finite
exact nonzero-block support from
`commutingTupleGeneralizedWeightDecomposition`, before introducing v, ell
or n. It reconstructs v by the preceding finite-coordinate lemma, applies
the actual action and ell by linearity, and uses the supplied compatibility
`B ⟨c,q⟩ = (b c q : V)`. Substituting `functional_block_action`, expanding
evaluation through the published coefficient-polynomial double sum,
interchanging the two finite local sums and rearranging complex scalars
gives the exact stated coefficient contraction. The polynomial is precisely
`generalizedWeightCoefficientPolynomial A c (b c) B v ell`.

## Simultaneous witnesses and exact scope

`commutingTupleGeneralizedWeightPolynomialAssembly` obtains actual
compatible local bases b and ambient basis B from
`commutingTupleGeneralizedWeightGlobalBasis`. Applying the coefficient
theorem to that pair supplies s and the identity for every v, ell and n.
The final theorem conjoins these three closed components.

All components retain arbitrary carrier universe u, every natural lattice
rank, finite-dimensional complex modules, every unit label and every
integer coordinate of either sign. Zero spaces, zero blocks and lattice
rank zero require no separate hypotheses: empty finite sums and ordered
products have their usual values, and a zero block has no local index.
The functional is algebraic and complex-linear, with no conjugation or
topological assumption. The finite support and simultaneous witnesses are
chosen before all coefficient inputs. No uniqueness, minimal truncation,
basis independence or degree bound is asserted.

This unit proves the published three-clause aggregate. Worker 1214's
separate occurring-character proof branch and all other Appendix and book
obligations remain outside this result.
