# Subgroup-test construction of the compact Hecke comparison

Worker 133, Task 5403. Internal construction for Renard III.2.6, printed
pp.75–76 / PDF pp.81–82, registered source
`renard-2026-representations-groupes-reductifs-padiques`.

For a closed subgroup H, `compactSubgroupTest H hH g T` is the actual subgroup
test function b_g(h)=χ(h)T(g⁻¹h), where χ=ΔH/ΔG restricted to H. Closedness of H
ensures compact support of this restriction. It depends complex-linearly on T.
Left covariance of these tests gives covariance of their integrated action,
with exactly the published relative twist. A common compact-open left
stabilizer of T gives a single right stabilizer of the resulting function.
The values use the existing algebraic finite-fiber integral and impose no
topology on the representation carrier.

If a comparison value at g is nonzero, some h in H satisfies T(g⁻¹h) ≠ 0.
The class of g therefore lies in the image, in H\G, of the inverse support
of T. This image is compact. The projected support of the smooth covariant
function is closed by the existing induction support lemma, so it is compact.
`compactComparisonFunction` consequently lands in the original
`Induction.CompactFunctions` carrier.

`compactComparisonBilinear` bundles complex linearity in both T and w.
These laws follow from linearity of restriction and weighting on the subgroup,
and from the published linearity of `integratedAction`; equality in the
compact-function space is checked pointwise.

This unit constructs the elementary compact-function map. Balancing over the
subgroup Hecke algebra, ambient Hecke equivariance, the prescribed scalarized
inversion formula, and bijectivity remain separate obligations.
