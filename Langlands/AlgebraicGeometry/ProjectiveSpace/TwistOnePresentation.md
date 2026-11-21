# The native projective presentation of the degree-one twist

`twistOneProjPresentation R m` is a `Scheme.Modules.ProjPresentation` of the
actual module `twistOne R m` over the affine base `Spec R`. It uses the `m+1`
coordinate sections `twistOneCoordinate R m` and the identity map to the
polynomial projective space. This specifies the module used by a caller such
as `hilbertSchemeUniversalFamily`; it does not just assert existence of some
module presenting projective space.

- The presentation is over `Spec R` since its projective map is the identity.
  On every open contained in `D₊(X i)`, multiplication by the restriction of
  `X i` is bijective by `ProjTwist.bijective_smul_restrict_section`.
- The ratio in `ProjPresentation` is the same degree-zero section `X j / X i`
  as `projectiveSpaceCoordinateRatio`. With the identity projective map, the
  ratio axiom is exactly the coordinate restriction identity proved by
  `twistOneCoordinate_restrict_coordinateOpen`.
- `twistOne_isInvertible` converts the published local rank-one result for
  `𝒪(1)` to `Scheme.Modules.IsInvertible` using the comparison of restriction
  and pullback along open immersions. `twistOne_closedImmersionBySections`
  packages the presentation with the closed-immersion instance for the
  identity.

This is a derived interface between `ProjectiveSpace/TwistOne.lean`,
`ProjectiveSpace/TwistOneLocalFramesProof.lean`, and the ported
`Def_AlgebraicGeometry_ModulesProjPresentation.lean`. It uses the same
polynomial grading and homogeneous fractions as those definitions. The
construction imposes no noetherian or field hypothesis on `R`.
