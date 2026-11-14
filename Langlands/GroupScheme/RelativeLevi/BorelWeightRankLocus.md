# The clopen locus with no opposite nonzero adjoint weight ranks

Worker 647. The internal definition
`Langlands.GroupScheme.splitTorus.noOppositeWeightRankLocus` applies to a
smooth affine group scheme `P` over an arbitrary affine base `Spec r`,
with a specified homomorphism from the standard split torus of finite
coordinate type `I`. It is the set of points `s` such that, for every nonzero
integral vector `m : I → ℤ`, at least one of the actual geometric-fibre
character weight dimensions at `m` and `-m` vanishes.

The definition uses the published
`splitTorus.geometricExponentWeightRankProfile`, so its dimensions are those
of the actual Lie weight spaces of the actual scheme-theoretic geometric
fibre, with the canonical split-torus base-change comparison.

The theorem `isClopen_noOppositeWeightRankLocus` follows directly from
`isLocallyConstant_geometricExponentWeightRankProfile`. The locus is the
preimage of a subset of the set of all rank profiles; its complement is the
preimage of the complementary subset. Both preimages are open.

The supporting module `RelativeLevi.BorelWeightRecognition` proves the field
recognition needed for the intended Borel-locus application. Its final theorem,
`splitTorus.isBorelSubgroup_iff_no_opposite_exponent_weight_finranks`, gives
exactly the same numerical criterion over an algebraically closed field when
`P` is a parabolic subgroup of a connected reductive group and the specified
torus is maximal in the ambient group.

These are derived definitions and helper theorems using published Library
results. This module alone makes no assertion equating the defined locus with
the residue-field Borel locus over an arbitrary base. That comparison also
needs the relative parabolic hypotheses, an appropriate ambient maximal
torus, and the geometric-fibre transport.
