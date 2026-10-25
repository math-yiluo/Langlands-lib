# Prescribed-vector cyclic extraction

This module proves the exact published proposition
`Langlands.TwoFactorCyclicExtractionStatement` by the theorem
`Langlands.twoFactorCyclicExtraction`. The two group universes `uG₁`, `uG₂`
and the carrier universe `uV` are independent. The target statement and all its
imports are unchanged. The representation is an admissible irreducible complex
representation of the actual direct product; the proof constructs the required
cyclic subrepresentations inside its original carrier.

## Prescribed-vector refinement

`CyclicExtraction.exists_cyclic_in_span` localizes the published internal
minimal-fixed-space argument of `TwoFactorExistence.exists_cyclic` to the
first-factor orbit span of the prescribed nonzero vector `x`.
Smoothness gives a product of open subgroups fixing `x`, with the first subgroup
chosen compact. Their simultaneous fixed space `M` is finite dimensional by
admissibility of the product representation. Among nonzero vectors `z` lying in
both `M` and the first-factor orbit span of `x`, choose `y` minimizing the
dimension of the intersection of `M` with the first-factor orbit span of `z`.
The initial vector `x` ensures that the minimization set is nonempty.

For any nonzero `u` in the orbit span of `y`, the published compact-averaging
lemma `exists_fixed_of_ne_bot` supplies a nonzero first-subgroup-fixed vector
`n` in the orbit span of `u`. It is also fixed by the second subgroup, since
that fixed space is preserved by the first action. Hence `n` lies in `M` and
in the orbit span of `x`. The intersection attached to `n` is contained in the
one attached to `y`; minimality and finite dimension make them equal. Thus
`y` belongs to the orbit span of `n`, and consequently to that of `u`.
The resulting regeneration property gives irreducibility.

`CyclicExtraction.refinement` packages this argument using the target's
`Cyclic.orbitSpan`. The published `isAdmissible_of_le_secondFixed` gives
admissibility of the new cyclic representation because its whole carrier is
fixed by the second open subgroup. Membership of `y` in the orbit span of the
original `x` is retained throughout, rather than deduced from an unrelated
irreducible subrepresentation.

## Spherical prescribed vectors

`CyclicExtraction.spherical` first uses the published
`admissibleProductFactorization` to obtain admissible irreducible factors
`σ` and `τ` and an actual intertwining equivalence. `firstTensorEquiv` restricts
that equivalence to the first group: the second tensor coordinate then carries
the trivial action. Let `t` be the image of the prescribed vector `x` under
this restricted equivalence. It is nonzero and `H`-fixed.

Choose a basis of the second tensor space. The published equivariant maps
`TensorMultiplicity.coefficient` show that every first-factor coefficient of
`t` is `H`-fixed. One coefficient is nonzero by
`TensorMultiplicity.exists_coefficient_ne_zero`, so the first factor has a
nonzero fixed space. The given `SphericalHeckeCommutative` hypothesis makes
the actual corner `HeckeAlgebra.Corner μ H hH` commutative: apply its faithful
homomorphism `toHeckeAlgebra` to the two products and use the given convolution
identity on their bi-invariant representatives. The published
`Hecke.finrank_fixedVectors_eq_one_of_corner_comm`, with admissibility and
irreducibility of `σ`, now makes its `H`-fixed space one dimensional.

The internal helper `exists_tmul_of_fixed_line` reconstructs a fixed tensor
from its finite basis expansion. For any chosen nonzero fixed vector `u` in
the first factor, every coefficient is a scalar multiple of `u`, by
`finrank_eq_one_iff_of_nonzero'`. Moving these scalars to the second tensor
coordinate and summing gives `t = u ⊗ w`. Thus the original `x` is the image
of `u` under the intertwiner obtained by composing `TensorMultiplicity.slice σ w`
with the inverse restricted equivalence. This intertwiner is nonzero since it
sends `u` to `x`; Schur's injectivity lemma makes it injective.

`orbitSpan_eq_top` states that a nonzero vector generates an irreducible
representation. `cyclicImageEquiv` uses this fact and
`FiniteVectors.map_orbitSpan` to corestrict an injective intertwiner to an
equivalence with the cyclic representation of the image vector. Applied to
the preceding slice, it identifies `σ` with the first-factor orbit span of
this same `x`. Admissibility transports by `isAdmissible_of_equiv`.
The internal `irreducible_of_equiv` transports irreducibility through the
corresponding bijective linear map of group-algebra modules. Finally,
`fixedVectorsEquiv` transports the one-dimensional fixed-space calculation.
No whole first-factor restriction is asserted to be irreducible or admissible.

## Provenance

These are internal derived consequences of Flath's two-factor theorem and the
commutative-corner fixed-line argument, rather than verbatim numbered results
with the names used here. The original background is D. Flath,
*Decomposition of representations into tensor products*, Proceedings of
Symposia in Pure Mathematics 33, part 1 (1979), printed pp.179–183, registered
as `flath-1979-tensor-products`. The retained original is
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`,
SHA256 `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
Printed p.179 (one-based PDF p.175) gives the fixed-space corner argument;
p.180 (PDF p.176) proves Theorem 1; and p.181 (PDF p.177) contains Example 2
and Theorem 2. Those pages were read for this derivation. No applicable source
errata was found in the supplied public locations. The module reuses the
published formal proofs of the two-factor and fixed-line inputs; its new
arguments are the localized minimization, tensor coefficient reconstruction,
and cyclic-image transport described above.
