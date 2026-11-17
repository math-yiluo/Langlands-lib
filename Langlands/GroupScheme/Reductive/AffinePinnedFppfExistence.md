# Actual fppf pinned corrections of arbitrary comparisons

For any affine pinned models `M`, `N`, arbitrary common scheme `T` with base
maps `f`, `g`, and actual comparison `e`, the construction
`AffinePinnedModel.fppfPinnedCorrection e` gives an actual
`FppfPinnedCorrection e`. Thus it supplies a single flat, surjective, locally
finitely presented map `p : U ⟶ T`, an actual target-group section on `U`,
and a proof that the original normalized pulled-back comparison followed by
its inner conjugation is `IsLocallyPinned`.

The concretely pinned comparison preserves the specified coordinate tori and
canonical positive-coroot cocharacters, and its actual differential carries
the original pinning vectors to the relabelled target vectors on every local
affine test. The construction imposes no extra hypotheses. In particular,
the common scheme and its refinements may be disconnected, nonaffine, empty
or not quasi-compact.

The theorem `fppfLocalPinnedNormalizationExistence` proves the exact
`FppfLocalPinnedNormalizationExistenceStatement` in every universe. It
includes the actual source section `c` and the equation
`innerIso c = pullComparison e p ≪≫ d.symm`, where `d` is the concretely
pinned comparison.

This is an internal final assembly of the existing actual affine pinning
correction and arbitrary-base cover constructions:

1. `hasAffineBasedPinnedCorrections` starts from a supplied algebra-based
   `BasedCoordinateIso`. Its actual commutative torus isomorphism and
   inclusion square are `commTorusIso` and `commTorusIso_square`.
   `simpleEquiv` and `simpleCharacter_congr` supply the required
   source-to-target simple-root relabelling and actual character equations.
   `cocharacter_comp` supplies the exact canonical cocharacter equation.
2. Apply `exists_fppf_pinnedCorrection_of_aligned` to these data. Its
   all-test inverse-unit torus correction supplies the actual cover and
   target section. Pack the flatness, surjectivity, local finite
   presentation and concrete pinning proof as `FppfPinnedCorrection`.
   This discharges the affine input previously retained by the global
   assembly.
3. `fppfPinnedCorrection` applies
   `FppfPinnedCorrection.ofAffineBasedInput` to this proved input.
   That construction first uses affine etale based-correction charts,
   applies step 2 chartwise after recovering the two algebra structures
   from the actual affine maps, absorbs the initial target corrections,
   and composes and collapses the covering families with their actual
   sections.
4. The earlier theorem
   `fppfLocalPinnedNormalization_of_affineBasedPinnedCorrections`
   then gives the stated local-normalization theorem, including its exact
   source-conjugator equation.

The module establishes geometric local normalization. The canonical global
comparison operation and its identity, composition, arbitrary-pullback and
adjoint-section laws use the separate rigidity, independence and descent
results; they are not asserted by this module alone.
