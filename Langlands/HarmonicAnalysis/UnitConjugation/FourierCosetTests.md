# Fourier transforms of lattice coset tests

For a self-dual bicharacter `e` and an additive Haar measure `μ` on a topological abelian group with its Borel σ-algebra, the Fourier transform of the indicator of `z + L`, with `L` a compact open additive subgroup, is `μ(L) e(x,z)` on the annihilator of `L` and zero elsewhere. `FourierLatticeCosetStatement` expresses the formula on Schwartz–Bruhat tests. `pairingFourierSB_latticeCosetTest_apply` applies it to the symmetric nondegenerate bilinear pairing and continuous additive character used for Lie-algebra distributions.

The proof translates the integration variable by `z`. The translated test is the indicator of `L` by the quotient-group description of cosets. Multiplicativity in the translated variable extracts the factor `e(x,z)`, and `BicharacterFourier.Internal.bicharacterFourier_indicator` gives the result. For the dual-lattice cosets of Clozel's formula, the double-annihilator identity then places these Fourier tests on the original lattice.

Clozel, *Characters of non-connected, reductive p-adic groups*, Canadian Journal of Mathematics 39 (1987), §3.8, printed pp. 165–166, uses this computation with `L = Λ*` in the proof of Lemma 15.
