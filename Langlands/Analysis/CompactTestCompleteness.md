# Completeness of the space of smooth functions supported in a fixed compact set

Let the domain be a real normed space, the target a real Banach space,
and \(K\) a compact subset of the domain. The space of smooth functions
supported in \(K\) is complete in its existing Mathlib uniformity, and
its topology is Baire.

Mathlib embeds the space uniformly into the countable product of the
Banach spaces of bounded continuous derivative profiles. To show the
image is closed, consider a convergent sequence in the image. Each
derivative converges uniformly. The uniform limit theorem for Fréchet
derivatives identifies the derivative of each limiting profile with
the next one, after currying. Induction makes all profiles the iterated
derivatives of the limit in degree zero. This function is smooth and
vanishes outside \(K\) by pointwise convergence.

The internal proof transfers completeness along the uniform embedding,
and complete pseudometrizability along the closed embedding. The
countable product and its closed subspace satisfy the Baire theorem.
