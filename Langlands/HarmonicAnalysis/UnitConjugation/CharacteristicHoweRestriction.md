# Conic restriction after enlarging the frequency lattice

`CharacteristicConicFiniteness` gives a single positive cone parameter `δ`. For each compact open additive subgroup `L`, it requires a compact open additive subgroup `M` containing `L` that works for every bound `b > 0`. Consider the conjugation-invariant distributions vanishing on indicators of `x + M` with `‖x‖ > b` and `x` outside `characteristicCone F δ`. The hypothesis asserts finite dimensionality of their image under restriction to `M`-invariant tests.

`CharacteristicHoweRestrictionStatement` works over a complete nontrivially normed ultrametric field `F` in a finite-dimensional normed `F`-algebra with a proper ultrametric norm metric. It assumes `1 < ‖d‖`, conic finiteness and containment of the unit characteristic sublevel in the unit-conjugation saturation of a compact set. For the resulting positive cone parameter, suppose a conjugation-invariant distribution has the large-center vanishing at a compact open lattice `L`. It then agrees on tests invariant under an enlarged compact open lattice `M` with a conjugation-invariant distribution supported in the closure of the unit-conjugation saturation of a compact set.

For a large center outside the cone, every point in its coset of `M` is still large and outside the cone. The coset indicator of `M` is invariant under the smaller lattice. Multiplication by the indicator of that coset sends each smaller coset indicator either to itself or to zero. In the first case its center lies in the coset of `M`, giving zero evaluation by the smaller-lattice vanishing. The span of smaller coset indicators therefore gives zero evaluation at the larger coset. The characteristic exhaustion then gives a matching distribution on the enlarged lattice.

This combines the lattice restriction and cutoff steps in the extension of Howe's theorem. [Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, §§11.1–11.2, pp. 58–62](https://doi.org/10.1090/ulect/016)

`CharacteristicHoweRestrictionCompleteUltrametricStatement` makes the completeness, ultrametric and properness hypotheses explicit.
