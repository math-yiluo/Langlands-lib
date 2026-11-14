# Integral root and dynamic-centralizer generation

This internal derived unit applies the actual integral root-product charts of
`LocalRootProducts` to subgroup containment on test schemes, and combines the
two signs with `Dynamic.HenselianCellGeneration`. The construction retains
arbitrary universe `u`.

`range_le_of_orderedProductIso` transfers containment of the points of the
original ordered root factors across a supplied scheme product chart whose
composite into the ambient group is the original ordered multiplication.
It works over any scheme, on any test scheme, and includes the empty product.
The proof evaluates the chart inverse and uses the finite ordered point-product
formula.

`dynamicUnipotent_carrier_le_of_exponentRoots` assumes a local domain `R`,
a field `R`-algebra `k`, a smooth affine ambient group with geometrically
connected fibres, and a map from a finite coordinate split torus. Its
base change to `k` must be monomorphic and have an actual relative root
system. For any test scheme `T`, a subgroup of `G(T)` containing every
integral fixed-exponent root functor whose exponent is a root on this field
fibre contains every point of the dynamic radical of any fixed-exponent
cocharacter.

The proof enumerates the indivisible positive roots on the field fibre.
The relative root system gives disjoint positive rays. The domain root
construction supplies actual smooth integral representatives for the
nonzero enumerated characters. `LocalRootProducts` then supplies their
scheme product chart onto the actual dynamic radical. Evaluating this chart
on `T` and using the given root containments proves the assertion.

`exponentRootCentralizerSubgroup` is the supremum of the actual integral
root-section subgroups selected by roots on the specified field fibre,
joined with the actual dynamic-centralizer section subgroup. It is the
smallest subgroup containing precisely these section subgroups.

`eq_top_of_exponentRoots_and_dynamicCentralizer` additionally assumes that
`R` is Henselian and its residue field is separably closed. A subgroup of
the integral section group containing those integral root functors and the
actual dynamic centralizer is the entire section group. The preceding
containment theorem applies to both signs of the exponent vector. Smooth
geometrically connected affine field fibres are geometrically integral,
so the ambient group has geometrically irreducible fibres. The published
Henselian triple-cell generation theorem then applies.
`exponentRootCentralizerSubgroup_eq_top` applies this criterion to the
constructed subgroup itself and proves that it is the full section group.

No integral reductivity, finite relative index, compactness or supplied
integral factorization is assumed. The field-fibre root-system and
monomorphy hypotheses are retained. For the parahoric application, one must
still provide the compatible integral torus and identify the generic
images of its integral root functors and dynamic centralizer with the
specified root and centralizer generators. This unit does not prove
`UnramifiedParahoricModelStatement`.
