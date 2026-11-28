# `Z(F)^0 = Z(F)^1` when the minimal Levi subgroup is a split torus

Module `Langlands.Geometry.Building.DepthZero.GeneralLinear.CentralizerZero`, namespace
`Langlands.Geometry.Building.GeneralLinearParahoric`.

Let `F` be a nonarchimedean local field, `K = UnramifiedClosure F`, and
`E : ZeroSubgroupDatum i j` data of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*,
Definition 2.6.23 for `G(F)^0`, with minimal Levi subgroup `j : Z → G` and
`Z(F)^0 = E.centralizerZero = Z(K)^0 ∩ Z(F)`.

## Declarations

- `isInducedTorus_of_isSplitTorus`: a split torus over a field `k` is induced
  (`IsInducedTorus`, KP Definition 2.5.1): the trivial extension `k / k` splits it, and its
  trivial Galois group fixes every `ℤ`-basis of the character lattice.
- `exists_torusIwahori_map_eq`: for data `C` of KP Definition 2.6.23(1) for `Z_K` with `Z`
  split, every point of `Z_K(K)^1` (the character-valuation kernel for the valuation of `K`) is
  the image under `C.i` of a point of the Iwahori subgroup `C.torusIwahori = T(K)^0`.
- `rationalCommonNormKernel_le_centralizerZero`: if `Z` is a split torus, then
  `Z(F)^1 ≤ Z(F)^0`.
- `map_rationalCommonNormKernel_le_zeroSubgroup`: in that case `j(Z(F)^1) ≤ G(F)^0`.

## Proofs

`exists_torusIwahori_map_eq`: `Z_K` is a split torus (`IsSplitTorus.baseChange`), so the
supplied maximal torus `C.i : T → Z_K` is an isomorphism (`IsMaximalTorus.isIso_of_torus`).
Hence `T` is split and induced, and KP Lemma 2.5.18 over `K` (`inducedTorusIwahori`) gives
`T(K)^0 = T(K)^1`. The preimage of a point of `Z_K(K)^1` under the isomorphism lies in `T(K)^1`
(`map_characterValuationKernel_le` for the inverse).

`rationalCommonNormKernel_le_centralizerZero`: a point `z ∈ Z(F)^1` extends to a point of
`Z_K(K)^1` (`characterValuationKernelDescent_proof`, KP 2.6.16(4) and 2.6.17; `Z` is affine by
`ZeroSubgroupDatum.isAffine_centralizer`). By the previous lemma it is the image of a point of
`T(K)^0`, which lies in `Z(K)^0` (`UnramifiedZeroDatum.map_torusIwahori_le_zeroPoints`), so
`z ∈ Z(F)^0` by the definition of `anisotropicZeroPoints`.

With the inclusion `Z(F)^0 ≤ Z(F)^1` of `ZeroSubgroupDatum.centralizerZero_le_rationalCommonNormKernel`
this gives `Z(F)^0 = Z(F)^1` for split `Z`, the split case of KP Lemma 2.5.18 combined with KP
Definition 2.6.23(2).
