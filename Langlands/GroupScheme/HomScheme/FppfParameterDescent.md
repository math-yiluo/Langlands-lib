# Descending subgroup parameters along flat open test maps

`HomScheme.FppfParameterDescent.exists_good_open_of_flat` starts with
two actual closed subgroup families `j` and `i`, an affine test scheme
`T`, an affine scheme `E` with a flat map `e : E ⟶ T` locally of finite
presentation, and a parameter of `j` over `E` whose evaluated range
is that of the comparison family `i` over `T`. It assumes evaluation
of `j` is injective on affine tests. For any point of `T` in the
image of `e`, it constructs an open neighbourhood carrying an actual
parameter of `j` with exactly the prescribed evaluated subgroup.
Global surjectivity of `e` is not required.

`OpenParameter` packages the open neighbourhood, its membership of
the specified point, the actual parameter morphism, and its all-test
evaluation equation. `openParameterOfFlat` chooses the data supplied
by the existence theorem. Neither a torus nor a multiplicative-type
hypothesis is needed by these generic constructions, and no
hypothesis is imposed on the ambient group.

The map `e` is open by the published Mathlib theorem that a flat map
locally of finite presentation is universally open. Choose a basic
affine neighbourhood of the point inside its image. Its pullback
under `e` is a surjective flat map between affine schemes, hence a
quasi-compact effective epimorphism. Affine injectivity of evaluation
extends to all tests using the published generic
`TorusChart.injective_all_of_affine`. It makes the supplied parameter
constant along the two projections of this effective epimorphism,
so the parameter morphism descends. Finally,
`TorusChart.evaluate_eq_of_comp_fpqc` descends equality of the actual
closed subgroup ranges.

This is an internal adaptation of
`TorusChart.exists_good_open_of_etale` from `TorusChartOpen`. Its
proof needs only flatness and openness of the test map; the imported
universally-open theorem supplies the latter from local finite
presentation. It is intended for the fppf diagonalizable splitting
used by multiplicative-type subgroup charts and makes no
unconditional chart-existence claim.
