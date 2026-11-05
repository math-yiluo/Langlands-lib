# Central Cartan charts for the prescribed rational norm-kernel orthant

This internal adapter retains a supplied
`NormKernelFundamentalCocharacters` family throughout the ambient Cartan
decomposition. It concerns the actual rational points of the connected
reductive group over a nonarchimedean local field. No positive-rank or
characteristic restriction is imposed.

`normKernelCentralCartanChart d K₀ t` consists of the ambient points
`k₁ * (d.orthantHom(n) * t) * k₂ * z`, where the orthant point is included from
the actual common rational norm kernel, both compact-side factors belong to
the supplied subgroup `K₀`, and `z` belongs to the full abstract center of the
ambient rational-point group. Its definition does not assert compactness of
the subgroup or of the chart.

`exists_finite_centralCartanCover` uses the supplied apartment datum and point,
represented centralizer maps and their factorization of the torus inclusion,
same-compact standard-Levi compatibility, and finite lattice transversal.
Connected reductivity, maximal splitness, genericity, and the published
standard-cocharacter statement identify the full-index Levi with the whole
ambient group. The common kernel of all simple-root pairings evaluates into
the full center by `commute_uniformizerPowers` for that Levi.

The compatibility at the empty root set supplies the uniformizer valuation
formula. `exists_rep_rationalCartanSet` then gives a lower bound for all
simple-root coordinates, using the finite transversal. The supplied actual
Cartan decomposition has both outer factors in the same specified
`D.specialCompactSubgroup x`.

The prescribed-generator chamber lemma is applied with precisely
`d.cocharacter`. Standardness of this family supplies its positive diagonal
and zero off-diagonal pairings. It selects one finite set of residual
translates before all ambient points. The resulting natural generator sum
evaluates to the included value of `d.orthantHom`, by unfolding the two
definitions of the same intrinsic uniformizer section. The final central
factor and the order of all other factors are preserved.

`exists_finite_centralCartanFactorization` exposes the same cover as a literal
factorization, with the orthant exponent before the two subgroup factors and
finite translate. It only reorders existential witnesses.

The proof is algebraic on these supplied actual geometric data; it uses no
topological compactness assertion. In particular, it neither assumes nor
proves `SpecialCompactProperties`. The simple-root type may be empty, since
the finite chamber argument permits an empty sum. No compactness assertion
about the full central quotient is included.

The provenance is internal: the proof adapts the published actual
`rationalFiniteChamberCartanCover` argument of Worker 349, replacing its
existential choice of generators by the prescribed-generator refinement.
The corrected family and its kernel-valued evaluation come from Worker 1618's
positive-generator construction. This adapter does not construct the
same-compact geometric witness, a common Iwahori level, an actual kernel
residual cover, a Hecke sandwich, or uniform coefficient support.
