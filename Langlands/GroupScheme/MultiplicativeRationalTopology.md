# Continuous scalar-unit parametrization of multiplicative-group points

For a topological field `k`, the existing affine point equivalence identifies the `k`-points of the multiplicative group with `kˣ`. Its inverse is continuous from the units topology to the canonical affine rational-point topology. `Gm.rationalPointOfUnit` bundles this inverse as a continuous group homomorphism.

The proof uses the canonical isomorphism to the relative Laurent spectrum. A scalar unit gives the spectrum map induced by evaluating the Laurent variable at that unit. The underlying affine evaluation of each regular function is therefore evaluation of a fixed Laurent polynomial. A Laurent monomial is continuous on units because taking an integer power in the units group and forgetting to the field are continuous. Finite sums preserve continuity. The canonical comparison between affine and rational points then gives continuity of the original scalar-unit map.

This is derived from the Library's multiplicative group and its affine evaluation topology. Together with the finite-algebra unit parametrization it gives the two continuous coordinates needed for the compact unit subgroup in Harris's split similitude group.
