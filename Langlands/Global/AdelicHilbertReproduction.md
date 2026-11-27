# Smooth reproduction of adelic Hilbert vectors at a fixed level

`exists_archimedean_smooth_convolution_of_adelicFinite` applies to a nonzero
vector `w` of an irreducible continuous unitary representation of `G(𝔸)` with
finite-dimensional orbit span under an archimedean maximal compact subgroup
and fixed by an open subgroup `L` of the finite factor. It finds a compactly
supported smooth archimedean kernel `h` and an `L`-fixed vector `u` with
`w = ∫ x, h(x) π(x)u dx` over the archimedean group.

Let `T` be the closed subspace of `L`-fixed vectors with all scalar compact
profiles in the finite-dimensional space of profiles of `w`. The compact
weighted average `P` sends the `L`-fixed subspace into `T` and fixes `T`.
`integratedIsometricSmoothDensity` supplies archimedean-smooth approximants
in the `L`-fixed subspace. Applying `P` to them preserves smoothness by
`CompactSmoothAverage.isSmoothVector_orbitIntegral`. The resulting smooth
vectors are dense in `T`, and some are nonzero since `w` is nonzero.

`adelicSmoothCenterActsByScalar` applies
`ProductSmoothVectors.exists_smul_of_adjointInvariant` to the adelic product
action using `adelicEnvelopingCenterConjugation`. The finite-level smooth
subspace therefore has a common eigenvalue for the central element chosen by
`exists_reproducingKernel_of_centerEigenvalue`. Continuous linear functionals
are distributions of order zero, so `coefficient_envelopingAction` shows that
the corresponding matrix coefficients of smooth vectors from `T` satisfy
that eigenvalue equation. Their compact profiles belong to the prescribed
space by testing against the functional composed with the left operator.
The resulting continuous compact kernel `κ` reproduces every such coefficient
at the identity. Commuting the functional with the integral shows that the
integrated operator of `κ` fixes the smooth vectors in `T`, and boundedness
extends the identity to all of `T`.

Approximate `κ` uniformly by a smooth kernel `k` supported inside the same
compact set. Isometry bounds the difference of the two integrated operators
by the uniform error times the Haar mass of that set. The proof chooses the
error small enough that the integrated action of `k` followed by the
compact average `P` differs from the identity on `T` in norm by less
than one. The unit criterion for a Banach algebra makes that
operator surjective on `T`. For a preimage `u` of `w`, Fubini and left Haar
invariance move the compact average into the kernel. The average of the
left translates of `k` is smooth by compact parameter integration and has
compact support. This gives the asserted `h` and `u`.

The exact smoothing identity is the archimedean step of the reproducing
function construction in Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Lemma 9.7.2, pp. 264–265 (PDF pp. 276–277). Here it
is derived using Segal's scalar action and the uniform elliptic reproducer
on the closed subspace specified by the profiles. [Fixed-profile reproducer](AdelicFixedProfileReproduction.md)
[Segal's scalar action](../Representation/Archimedean/ProductSmoothInfinitesimalCharacter.md)
