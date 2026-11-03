# Splitting contractions through an injective product cell

This internal unit defines `Dynamic.HasProductContraction χ A B g`.
It asserts that a contraction of `g` along the affine line is a product of
two morphisms which belong to the subgroup functors `A` and `B` on the
whole affine-line test scheme.

Suppose that `A` and `B` are normalized by the range of `χ`, and multiplication
`A(X) × B(X) → G(X)` is injective for every test scheme `X`. Every such
product contraction splits into contractions of two factors of `g`, with
the factors belonging respectively to `A` and `B`.

Evaluation at one recovers the factors of `g`. Normalization puts the orbit
of each factor in its subgroup on the multiplicative-group test scheme.
Injectivity compares these two orbits with the restrictions of the
affine-line factors and makes each restriction the correct orbit.
At zero, their product is the identity. Comparing this product to the
pair of identity points gives identity zero values for both factors.

A further adapter turns an actual lift through multiplication of two
represented subgroup schemes into `HasProductContraction`. It uses the
range equalities in the representing inclusions and projects the lift.

Three common-group adapters prove the normalization needed in the torus
application. If two cocharacters `a` and `b` factor through the same
commutative group scheme `C` and `i : C → G`, then the range of `a ≫ i`
lies in the dynamic centralizer of `b ≫ i` on every test scheme.
The proof maps a commuting pair of `C`-points through `i` and simplifies
the conjugation orbit. Since the centralizer lies in the parabolic, and
the parabolic normalizes the unipotent subgroup, this range normalizes
both `P(b ≫ i)` and `U(b ≫ i)`. Precomposing `b` with inversion gives the
same conclusion for the opposite cocharacter. No closedness or torus
assumption on `C` is needed.

All results hold over an arbitrary base scheme in arbitrary universe `u`.
No affineness, separatedness, reductivity, representability or open-cell
theorem is assumed in the splitting result. The represented-lift adapter
retains its actual lift as a hypothesis. The normalization, all-test
injectivity and product-contraction hypotheses remain explicit.

The provenance is an internal consequence of the actual orbit-extension
definitions in `Dynamic.Basic`, their functoriality and the normalization
proved in `Dynamic.Decomposition`. The application to
an opposite open cell is part of the joint Bruhat proof strategy of Workers
1226 and 1262; this unit does not itself construct that open cell or prove
the full rational Bruhat theorem.
