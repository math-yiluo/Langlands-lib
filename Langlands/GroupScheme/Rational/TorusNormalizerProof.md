# Proof: smooth closed normalizers and centralizers of split tori

This module proves `TorusNormalizerRepresentableStatement` as `torusNormalizerRepresentable`, at an arbitrary universe `u`. Let `k` be a field, `G` a connected reductive group over `Spec k`, and `i : T ⟶ G` a split subtorus. Both `torusNormalizer i` and `torusCentralizer i` then have smooth closed representatives. No hypothesis is added: only smoothness and affineness of `G` (from `IsConnectedReductive`) and the split-subtorus hypothesis are used.

## Setup

- `hG.isAffineHom` and `isAffine_of_isAffineHom` make `G` affine, and `AffineCoordinates.smooth_algebra` (published `CorepresentedSmooth`) makes its coordinate algebra `B` a smooth `k`-algebra. `e` is the published corepresentation of the points of `G` by `B`.
- `IsSplitSubtorus` gives a finite index type `I`, an isomorphism `eT` of `T` with the split torus, and that `i` is a closed immersion. `exists_ideal_range` (published `NormalizerRepresentability`) gives an ideal `J` of `B` cutting out the range of `i` in affine coordinates.
- `dT` is the isomorphism from the published diagonalizable group `Diagonalizable.groupScheme k (I → ℤ)` to `T`, built from `Diagonalizable.splitIso` and `eT`. The composite `jD` of `dT` with `i` in affine coordinates is a closed immersion, hence a monomorphism.

## Normalizer

1. `diagonalizableEmbedding e jD` (from `Torus.NormalizerLifting`) is a character embedding of `I → ℤ` into the points of `G`. Its range over each algebra `A` equals the published family `affineSubgroups (range i) A`, by `diagonalizableEmbedding_range` and `SubgroupFunctor.range_iso_comp`.
2. `hasSquareZeroLifting_normalizerFamily` gives the square-zero lifting property of the algebra-level normalizer family of that range. The published `affineSubgroups_normalizer` identifies this family with the affine points of the all-test normalizer of `range i`.
3. The published `formallySmooth_of_hasSquareZeroLifting`, applied with `isCutOutBy_affineSubgroups_normalizer`, makes `B ⧸ subgroupNormalizerIdeal e J` formally smooth over `k`. It is finitely presented by `finitePresentation_quotient`, since `k` is noetherian and `B` is of finite type. So it is a smooth `k`-algebra.
4. `smooth_cutGroupScheme` turns this into smoothness of the cut-out group scheme. The published `AffineCoordinates.isClosedSubgroup_normalizer_range` and `AffineCoordinates.isRepresentedBy_normalizer_range` show that it is a closed subgroup representing `torusNormalizer i = (range i).normalizer`.

## Centralizer

The centralizer half is the published `torusCentralizer_hasSmoothClosedRepresentative` (module `Langlands.GroupScheme.Torus.CentralizerSmooth`, by Worker 1296). It is applied to `i`, the split-subtorus hypothesis and `hG.smooth`.

## Provenance

The statement is Milne, *Algebraic Groups* (2017), Propositions 1.83 and 1.92 together with Corollary 13.10, in the derived all-test formulation explained in `TorusNormalizerStatement.md`. The proof does not follow Milne's route for the normalizer. Milne obtains smoothness of `N_G(H)` from that of `C_G(H)` through equality of identity components. Here the infinitesimal lifting property of the normalizer is proved directly, by lifting the conjugation action on characters as a grouplike family and the point as a twisted transporter.
