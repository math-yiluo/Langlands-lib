# The Weyl element of the descended SL2 normalizes the torus

Module `Langlands.GroupScheme.Rational.OrthogonalOrbitWeylNormalizer`, namespaces
`Langlands.GroupScheme` and `Langlands.GroupScheme.SplitPinning`.

Worker 163, for Task 6836 (8c04a3ed-3fa6-4680-a59f-856738cb578b), SL2 half.

## Purpose

The SL2 clause of `AlgebraicRankOneCoordinatesExistenceStatement` requires
`C.rho SpecialLinear.BinaryUpper.weylMatrix ∈ normalizerPoints i`, where `i` is the
maximal split torus and `weylMatrix = !![0, -1; 1, 0]`. In Task 6836, `rho` is the
descended homomorphism `SplitPinning.fieldSL2 : SL₂(E) →* G(k)` of
`OrthogonalOrbitSpecialLinear`. This module proves that `fieldSL2` sends the Weyl matrix
into the normalizer of the torus `i : T ⟶ G` whose base change carries the pinning. It also
proves that such a point normalizes every maximal split torus factoring through `i`.

## Contents

- `weylWord_mul_weylMatrix`, `weylMatrix_inv_eq`: over a field,
  `weylMatrix⁻¹ = lower (-1) * upper 1 * lower (-1)`, by computing the entries.
- `map_weylMatrix`: ring maps fix the Weyl matrix.
- `SplitPinning.rootSL2_weylMatrix_mem`: for a split pinning `p` with normalized simple-root
  maps `x`, the rank-one homomorphism `rootSL2 x a` sends `weylMatrix` into
  `normalizerPoints p.inclusion`. Proof: by `weylMatrix_inv_eq`,
  `rootSL2 x a weylMatrix⁻¹ = y(-1) · x(1) · y(-1)`, with `y = negPoint` and
  `x(1) = unitPoint`. The Library's
  `NormalizedRootParametrization.isOppositeFactorPair_unitPoint` (module
  `NegativeRootPartner`) shows that this point normalizes the pinned torus. Normalizers are
  subgroups, so the inverse normalizes it too.
- `SplitPinning.orbitSL2_weylMatrix_mem`: the orbit product of Weyl matrices,
  `orbitSL2 (fun _ => weylMatrix)`, is a commuting product of such points. It lies in the
  normalizer by `Subgroup.noncommProd_mem`.
- `SplitPinning.mem_normalizerPoints_baseChange_of_pinning`: a normalizer point of the
  pinning inclusion `p.inclusion = eT.hom ≫ i_K` normalizes `i_K`, by the Library's
  `mem_normalizerPoints_groupHom_comp` applied to `eT.symm`.
- `SplitPinning.fieldSL2_weylMatrix_mem`: if `i` is a monomorphism, then
  `fieldSL2 … weylMatrix ∈ normalizerPoints i`. After scalar extension,
  `fieldSL2 weylMatrix` becomes `orbitSL2 (fun a => (τ a)(weylMatrix)) =
  orbitSL2 (fun _ => weylMatrix)` (`rationalExtend_fieldSL2`, `map_weylMatrix`). The Library's
  `mem_normalizerPoints_rationalExtend_iff` (module `NormalizerPointsRingEquiv`) descends
  membership to `k`.
- `SplitPinning.fieldSL2WeylPoint : normalizerPoints i` bundles `fieldSL2 … weylMatrix`
  with this membership (`fieldSL2WeylPoint_coe`).
- `IsMaximalSplitTorus.mem_normalizerPoints_of_mem_normalizerPoints`: let `T` be
  commutative, `j : T ⟶ G` and `s : S ⟶ T` with `s ≫ j` a maximal split torus. Then a
  rational point normalizing `j` normalizes `s ≫ j`. Its conjugate of `S` lands in the
  commutative `T`, so it commutes with `S`, and the Library's
  `IsMaximalSplitTorus.mem_normalizerPoints_of_commute_conjugate` (module
  `DerivedCoverNormalizerLift`) applies.

## Provenance

Internal. In `SL₂`, the Weyl element `!![0, -1; 1, 0]` normalizes the diagonal torus, and
the corresponding element of a rank-one subgroup normalizes a maximal torus. These are
standard facts. Here they are derived from the Library's opposite-factor-pair description of
normalizing points of a split pinning. No source theorem is cited. Every step is proved in
Lean.
