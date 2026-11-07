# Canonical negative-rho covariance

This is derived supporting work for the big-cell task. It defines the entire
canonical induced coordinate subspace and proves its positive-root invariance
and simple-coroot covariance on every relative test scheme. The arguments use
existing character evaluation, the actual dynamic limit morphism, and the
actual affine coordinate covariance equation; no external existence theorem is
introduced.

For a supplied split pinning `p`, a finite enumeration of its root index and the
hypothesis that the integral coroot span is the full cocharacter lattice, let
`rho` be its integral Weyl vector, let `nu` be its polarization, and put
`lambda = groupHom nu ≫ p.inclusion`. The actual affine parabolic model represents
`Dynamic.parabolic lambda`. The generic-centralizer theorem identifies the
original maximal torus with the dynamic centralizer. Its character `-rho`
extends to the parabolic by the actual Levi retraction. Write `chi` for the
affine coordinate of that extended character.

`SplitPinning.canonicalRhoCovariantSubspace hspan m` is exactly
`AffineCoordinates.leftCovariantSubspace (Dynamic.Affine.parabolicHom lambda)
(chi ^ m)`. Thus it is the full subspace of the original affine coordinate
algebra satisfying the left covariance equation. It is defined for every
natural number `m`, including zero; it is not a chosen finite subspace.

The general helpers first evaluate any torus character on a cocharacter as the
integer power prescribed by their actual lattice pairing. A point of the
dynamic unipotent subgroup has limit equal to the identity, so every character
extended from the centralizer evaluates to one there. Applying the coordinate
covariance equation proves left invariance under that unipotent subgroup for
every coordinate of the induced space for `chi ^ m`.

`canonicalRhoCovariantSubspace_left_root` specializes this invariance to any
intrinsic root subgroup whose root index is positive for the supplied base.
The lattice pairing of that root with polarized rho is positive, so the root
subgroup lies in the dynamic unipotent subgroup. The theorem
`canonicalRhoCovariantSubspace_left_linkedPositive` applies this to the fixed
positive map of `p.linkedRootParametrization r`, using its representation of
the entire intrinsic root functor. Both statements quantify over all coordinates
in the full subspace and all points of every relative test scheme.

`canonicalRhoCovariantSubspace_left_simpleCoroot` proves that left multiplication
by the actual simple-coroot point at a global-section unit `z` multiplies each
coordinate value by `(z⁻¹)^m`. Its general dynamic-parabolic version needs a
supplied root datum for the centralizer inclusion. The proof restricts the
extended character to the centralizer and uses the integral identity
`pairing (-rho) (simple coroot) = -1`. The explicit `id` in the displayed Lean
formula fixes the global-section codomain of evaluation and has no mathematical
effect.

All test schemes may be nonaffine or nonreduced, and the field has arbitrary
universe and characteristic. No infinite-field or algebraic-closure hypothesis
is used. The pinning and full integral coroot-span hypothesis remain supplied.
The module proves no induced-space dimension bound or irreducibility, and does
not construct the pinning or a highest-weight module. The full
`SteinbergBigCellStatement` remains a separate proof obligation.
