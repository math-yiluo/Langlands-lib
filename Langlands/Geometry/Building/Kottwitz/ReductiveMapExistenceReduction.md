# Formal descent for the reductive Kottwitz map

This conditional reduction develops the formal descent argument. It does not prove
`ReductiveKottwitzExistenceStatement` unconditionally. Its provenance is the
factorization argument in Kaletha–Prasad, *Bruhat–Tits theory: a new approach*
(2023), Lemma 11.5.1, printed p. 430 / PDF p. 461, source
`kaletha-prasad-2023-bruhat-tits-new-approach`. The corrections of 1 November 2024
have no entries for §§11.4–11.5.

`zExtensionPointMap` abbreviates the actual coefficient-point projection.
`zExtensionKottwitzComposite` composes the selected simply-connected-derived
map on the source with the actual selected inertia map. Its definition supplies
neither a square witness nor a kernel identity.

`zExtensionPointMap_mem_ker_iff` proves that the coefficient-point kernel is
exactly the image of the central torus on the same coefficient points. It uses
the all-test kernel equality in the definition of a z-extension and the actual
scheme-kernel point characterization, without requiring point surjectivity.
`zExtensionKottwitzComposite_kernel_iff` therefore reduces the kernel inclusion
needed for descent to vanishing of the composite on central-torus points.

The lemmas identify the square with equality of composed group homomorphisms.
Point surjectivity proves uniqueness from one square. Given the kernel
inclusion, Mathlib's `MonoidHom.liftOfSurjective` constructs the unique
homomorphism satisfying that square. A separate lemma proves surjectivity of
any square witness from surjectivity of the source Kottwitz map and the inertia
map. Epsilon specification is used only with an explicit existence proof.

The reduction's explicit inputs include general z-extension existence, the
simply-connected-derived cocenter construction, point and inertia
surjectivity, the kernel inclusion, and compatibility through common
z-extension refinements. None of these inputs is asserted here as
an unconditional theorem.

The module imports `SimplyConnectedDerivedKottwitzNaturalAt` from
`SimplyConnectedDerivedNaturalityReduction`, the actual
naturality square for a morphism between groups whose derived subgroups are
simply connected. `zExtensionPointMap_triangle` identifies the point maps of a
commuting triangle. `zExtensionKottwitzLawAt_compare` pulls two square witnesses
back along a common z-extension and proves equality using point surjectivity,
this upstairs naturality, and composition of the selected inertia maps.

`reductiveKottwitzExistenceAt_of_structural_inputs` then constructs all conjuncts
of the requested target at a fixed group. Its explicit assumptions are the
published simply-connected-derived statement and inertia-functoriality
statement; simply-connected-derived naturality; nonemptiness of z-extensions;
point and inertia surjectivity for each extension; annihilation of each
point-map kernel by the composite; and existence of a common dominating
z-extension for each pair. It constructs each individual descended map using
the kernel inclusion, compares these using the common refinement, obtains an
all-extension witness, and only then invokes epsilon specification. The
agreement with the simply-connected-derived map follows by naturality of the
projection and uniqueness from one square.

The companion `ReductiveMapStructuralReduction` derives kernel annihilation,
and `ReductiveMapTorusReduction` supplies the torus and cocenter inputs using
published proofs. `ReductiveMapRemainingInputs` packages the resulting
four-premise implication. This module alone asserts only the conditional
claims listed above.
