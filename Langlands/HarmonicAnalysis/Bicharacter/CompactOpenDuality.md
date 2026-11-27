# Annihilators of compact open subgroups for self-dual bicharacters

A compact open subgroup `L` of a topological abelian group with a self-dual bicharacter has a compact open annihilator. Openness is `IsSelfDualBicharacter.isOpen_annihilator`. The compactness proof uses the bound on the annihilator of a neighborhood of zero in the self-duality hypothesis and closedness of the open annihilator subgroup.

For a locally compact second countable group with a compact open exhaustion and its Borel σ-algebra, `compactOpenDoubleAnnihilator` proves `CompactOpenDoubleAnnihilatorStatement`. If `A` is the annihilator of `L`, then its annihilator is `L`. For any additive Haar measure, the Fourier transform of the indicator of `L` is `μ(L)` times the indicator of `A`. Applying the same formula a second time gives `μ(L) μ(A)` times the indicator of the annihilator of `A`. The Haar volumes are positive. Fourier inversion on Schwartz–Bruhat tests gives the reflected support `−L = L`, which yields the double-annihilator identity.

This follows from the Fourier indicator and inversion formulas used in Clozel, *Characters of non-connected, reductive p-adic groups*, Canadian Journal of Mathematics 39 (1987), §3.8, printed pp. 165–166. In the proof of Lemma 15 the Fourier transform of the indicator of the dual-lattice orbit is supported on the original lattice.
