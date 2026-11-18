# The matrix descent algebra of an actual reduced-norm-one group

This internal construction is a prerequisite for the Tits normalization of
the actual reduced-norm-one group `CentralSimpleUnits.normOne k A`. It does
not yet assert an equality with the general Tits obstruction, or identify a
fundamental weight.

Let `e : L ⊗[k] A ≃ₐ[L] Matrix I I L` be an actual splitting chart.
`matrixAction e` transports the canonical coefficient Galois action on
`L ⊗[k] A` across this chart. Its ring maps, scalar semilinearity and group
laws are proved. No independently supplied action, cohomology class or
effectivity premise occurs. `matrixAction_chart` states exact equivariance
of the chart.

For a finite Galois extension `L/k`, `fixedEquiv e` identifies `A` as a
`k`-algebra with the actual fixed matrix subalgebra. The forward map sends
`a` to `e (1 ⊗ a)`. Injectivity follows from faithful scalar extension;
surjectivity follows from the published fixed-tensor theorem
`GaloisAlgebraDescent.mem_range_includeRight_iff`. That theorem works for a
possibly noncommutative algebra factor.

`descentEquiv_fixedEquiv_tmul` shows that effective descent's multiplication
chart, composed with this algebra identification, is the original chart on
every pure tensor. `changeChart` and `changeChart_val` identify the fixed
algebras from any two charts over the same finite Galois extension by the
actual transition `f ∘ e⁻¹`. Thus chart independence is an explicit algebra
equivalence.

For an arbitrary central simple algebra, `canonicalMatrixAction` and
`canonicalFixedEquiv` use the published unconditional finite Galois
splitting field and its actual chart. There is no splitting-existence
hypothesis. Fields and central simple algebras lie in the same arbitrary
universe `u`. No characteristic, perfection or centre-smoothness condition
is imposed.

The mathematical context is Tits, *Representations lineaires irreductibles
d'un groupe reductif sur un corps quelconque* (1971), Theorem 3.3, printed
pp.203–204, where a projective representation is descended by twisting its
matrix algebra. Source
`provided-24a63a63d1d1f52de3bb06c78f1f0b8837e492ae9eb6ee738ba647284515e9d2`,
SHA-256
`dbab2ec31991b639ce5461e2fe0713ff4bc5f4b9f01dfcdcc24e1a0794c5edb9`.
This unit is an internal specialization of actual coefficient descent, not
a claim that Tits states these Lean interfaces verbatim. The general
obstruction comparison, first-fundamental-weight identification and
contragredient sign law remain separate obligations.
