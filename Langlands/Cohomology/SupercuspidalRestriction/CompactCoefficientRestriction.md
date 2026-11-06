# Compact coefficients on an open subgroup with compact central intersection

This module supplies two derived lemmas for the compact-coefficient step of
`CompactModCenterRestrictionStatement`. Let `G : Type uG` be a Hausdorff locally
compact topological group and let `H : Subgroup G` be open, with
`H ∩ Z(G)` compact. The lemmas require no normality or finite-index hypothesis.

`isCompact_centralQuotient_preimage_openSubgroup` proves that, for every compact
set `C` in the actual quotient `G / Z(G)`, its inverse image under
`H → G / Z(G)` is compact in `H`.

`hasCompactSupport_restrict_matrixCoefficient` considers a complex
representation `ρ` on `V : Type uV`, where `uV` is independent of `uG`. Assume
`HasCompactSmoothCoefficientsModCenter ρ`. For each vector `v` and each
algebraic linear functional `ℓ` smooth for the restricted dual action on `H`,
the matrix coefficient
`h ↦ ℓ (ρ h.val v)` has compact support in `H`. Smoothness and irreducibility
of `ρ` are not needed for this lemma.

The proof follows the coefficient argument in Bernstein–Zelevinsky (1976),
§3.21, implication (3) ⇒ (4), printed p.35 (the theorem begins on p.34):
restriction to an open subgroup preserves which algebraic dual vectors are
smooth, and coefficients restrict as functions. Their subgroup `G°` is
replaced here by an arbitrary open `H` satisfying the compact central
intersection hypothesis. The source's word “finite” means compact
smooth-dual coefficients in this passage, not finite dimension.

The topology argument is an internal derivation using
`Langlands.compactKernelProperMap`. The center is closed since `G` is
Hausdorff. The image of `H → G / Z(G)` is an open subgroup, hence closed. The
corestricted map from `H` to that image is an open continuous surjective group
homomorphism, with compact kernel identified with `H ∩ Z(G)`. Both groups are
locally compact. Compact-kernel properness gives compact preimages of compact
sets in the image, and its closed embedding into `G / Z(G)` permits applying
this to `C`.

For the coefficient lemma, `isSmoothVector_restrict_open_iff` applied to
`ρ.dual` makes `ℓ` a smooth vector for the ambient dual. The assumed
compactness modulo the center supplies a compact set `C` containing the
quotient image of every group element at which that coefficient is nonzero.
The support of the restricted coefficient lies in the compact inverse image
just proved. `HasCompactSupport.of_support_subset_isCompact` takes its
closure in the Hausdorff subgroup and concludes compact support. The proof
does not assume the coefficient itself descends to the central quotient.

Source: I. N. Bernstein and A. V. Zelevinsky, *Representations of the group
GL(n,F), where F is a non-Archimedean local field*, Russian Mathematical
Surveys 31:3 (1976), 1–68, §3.21, pp.34–35; registered literature ID
`bernstein-zelevinsky-1976-representations-gln`, source SHA-256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
