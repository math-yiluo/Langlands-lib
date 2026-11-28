# Characteristic cutoffs and their constancy on large lattice cosets

The open set `characteristicCone F δ` consists of points whose characteristic size is less than `δ` times their norm. It is stable under every nonzero scalar rescaling. For `δ > 0` it contains the nilpotent points of any closed norm annulus avoiding zero. On a compact set, the points in a sufficiently narrow characteristic cone belong to any prescribed open neighborhood of the nilpotent points of that set. This follows by bounding the norm on the compact set and taking the positive minimum of the characteristic size on the compact complement of the neighborhood.

`LargeCharacteristicCosetStatement` takes a complete nontrivially normed ultrametric field `F` and a finite-dimensional normed `F`-algebra with a proper ultrametric norm metric. Given `d ∈ F` with `1 < ‖d‖` and a positive cone parameter `δ`, each compact additive subgroup `L` has a positive threshold. For any center `x` of norm strictly above that threshold and outside the cone, every `x + l` with `l ∈ L` has the same norm and characteristic size as `x`.

The ultrametric inequality gives equality of norms once `‖x‖` exceeds the bound on `L`. A power of `d` rescales `x` into the compact annulus of norms between `1 / ‖d‖` and `1`. The annular points outside the cone have positive characteristic size, so local constancy and the tube lemma give a uniform radius for perturbation there. For sufficiently large `‖x‖` this radius contains the rescaled `l`, and homogeneity cancels the rescaling in the two characteristic sizes.

This is the characteristic cutoff estimate used to preserve the Fourier coset vanishing condition under invariant cutoffs. [Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, §11.2, Lemmas 11.5–11.7, pp. 60–61](https://doi.org/10.1090/ulect/016)

`LargeCharacteristicCosetCompleteUltrametricStatement` makes the completeness, ultrametric and properness hypotheses explicit.
