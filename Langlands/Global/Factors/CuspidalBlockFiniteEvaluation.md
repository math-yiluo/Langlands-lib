# Evaluation in the actual cuspidal finite Levi factors

`realizedFiniteEvaluation` takes cuspidal block realizations over a number field with compact additive adelic quotient. The block sizes sum to the ambient rank. It requires a spectral presentation of each block whose local components are irreducible and admissible at every finite place, including the exceptional places.

The normalized local inducing sections use the references from these presentations. The adelic evaluation regroups the local Levi coefficients into finite block tensors. The irreducibility and admissibility hypotheses identify each block tensor equivariantly with the finite factor in the corresponding cuspidal realization's finite and infinite decomposition. Taking the external tensor of these equivalences sends the evaluation to the actual finite Levi coefficients.

The evaluation record carries the map, finite right translation, normalized parabolic covariance, and joint separation on the finite integral subgroup. These properties pass through the coefficient equivalence at the level of abstract Levi representations. The cuspidal specialization uses the existing additive groups of the actual local and finite factors.

This is a derived evaluation construction for the finite part of the restricted tensor product in Langlands, *On the notion of an automorphic representation* (1979), Lemma 1, printed p. 203, Corvallis Part I PDF p. 198. That passage specifies the local inductions and the choice of nonzero spherical reference vectors outside a finite set.
