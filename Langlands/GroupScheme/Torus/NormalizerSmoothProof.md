# Proof: smooth closed normalizers of arbitrary field tori

`Langlands.GroupScheme.torusNormalizerSmoothClosed.{u}` proves exactly
`Langlands.GroupScheme.TorusNormalizerSmoothClosedStatement.{u}`. Over every
field `k : Type u`, for every smooth affine group scheme `G`, commutative
group scheme `T`, and closed homomorphism `i : T.toGrp ⟶ G` with
`IsTorus T.toGrp`, it supplies an actual smooth closed subgroup representing
`torusNormalizer i` on every scheme test. All hypotheses and the conclusion
are those of the imported statement.

The proof first establishes smooth closed representability for a split
torus in a smooth affine ambient group. It then constructs a closed
representative over `k`, proves its smoothness after a splitting extension,
and descends smoothness to `k`.

## The split helper

`normalizer_hasSmoothClosedRepresentative_of_isSplitTorus` takes group
schemes `G` and `T` over a field, a homomorphism `i : T ⟶ G`,
`IsSplitTorus T`, `IsClosedSubgroup i`, and the two ambient assumptions
`Smooth G.X.hom` and `IsAffineHom G.X.hom`. It proves
`(SubgroupFunctor.range i).normalizer.HasSmoothClosedRepresentative`.
This helper is adapted from the normalizer half of Worker 950's published
`torusNormalizerRepresentable` in
`Langlands.GroupScheme.Rational.TorusNormalizerProof`. That argument only
uses smoothness and affineness of the ambient group.

Let `B` be `AffineCoordinates.algebra G` and `e` its corepresentation.
`AffineCoordinates.smooth_algebra` makes `B` smooth over `k`.
`exists_ideal_range`, applied to `AffineCoordinates.coordinateHom i`,
provides an ideal `J` describing the closed torus in these coordinates.
The split-torus isomorphism and `Diagonalizable.splitIso` give an
isomorphism `dT` from the diagonalizable group with character group
`I → ℤ` to `T`, for a finite index type `I`. Its composite `jD` with the
coordinate homomorphism is a closed immersion, hence a monomorphism.

`diagonalizableEmbedding e jD` gives a character embedding `emb`.
`diagonalizableEmbedding_range` and `SubgroupFunctor.range_iso_comp`
identify its range over every algebra with the affine points of the range
of the coordinate homomorphism. The imported
`hasSquareZeroLifting_normalizerFamily` supplies square-zero lifting for
its normalizer family. `affineSubgroups_normalizer` identifies that family
with the affine points of the all-test normalizer.

The quotient `B ⧸ subgroupNormalizerIdeal e J` is formally smooth by
`formallySmooth_of_hasSquareZeroLifting`, using
`isCutOutBy_affineSubgroups_normalizer`. It is finitely presented by
`finitePresentation_quotient`: the smooth algebra `B` is of finite type
over the noetherian field `k`. Thus the quotient is smooth.
`smooth_cutGroupScheme` makes its group scheme smooth, while
`AffineCoordinates.isClosedSubgroup_normalizer_range` and
`AffineCoordinates.isRepresentedBy_normalizer_range` supply its closed
inclusion and its representation of the normalizer on every scheme test.

## A splitting extension and descent

For the main theorem,
`hasClosedRepresentative_normalizer_centralizer_range i hi` first gives
a closed subgroup `j : N ⟶ G` representing the all-test normalizer over
`k`. Only its normalizer component is used.

The definition of `IsTorus` supplies a field extension `K/k` over which
`T` becomes split. Write `b : Spec K ⟶ Spec k` for its spectrum map.
`fieldExtension_fpqc` proves that `b` is surjective, flat and
quasi-compact. No finiteness or Galois property of the extension is needed.
Smoothness and affineness of `G` persist under this base change, as does
the closed immersion `i`. The split helper therefore supplies a smooth
closed representative `j' : N' ⟶ G_K` of the normalizer over `K`.

The base-changed inclusion `j_K` represents the same normalizer:
`SubgroupFunctor.range_baseChangeHom` identifies the range of `i_K`,
`SubgroupFunctor.normalizer_baseChange` commutes its all-test normalizer
with base change, and `hrep.baseChange b` transports the original
representation. Thus `hrepb.isoOfIsRepresentedBy hrep'` gives an actual
group-scheme isomorphism `N_K ≅ N'`. Forgetting to schemes over `Spec K`
and applying `smooth_of_over_iso` proves that `N_K` is smooth.

Finally Mathlib's
`MorphismProperty.of_pullback_snd_of_descendsAlong`, for smooth morphisms
and surjective flat quasi-compact covers, descends this smoothness to
`N → Spec k`. The original `j`, its closed-immersion proof, and its
all-test representation proof complete the required representative.
Every comparison is an equality or representation of subgroup functors
on all scheme tests, including nonaffine tests.

## Imported inputs and provenance

The target is imported from
`Langlands.GroupScheme.Torus.NormalizerSmoothStatement`.
`NormalizerRepresentability` supplies the coordinate ideals, closed
representatives and affine-to-all-tests comparisons.
`Torus.NormalizerLifting` supplies the diagonalizable embedding and
normalizer lifting theorem, using the published grouplike and twisted
transporter lifting infrastructure.
`SubgroupFunctor.NormalizerBaseChange` supplies normalizer base change;
its imports supply range and representative base change and uniqueness
of representatives. `BaseChangeReflection` supplies
`fieldExtension_fpqc`, `SmoothProducts` supplies `smooth_of_over_iso`,
and Mathlib's `Morphisms.LocalFlatDescent` supplies smooth descent.

The original source is SGA 3, Exposé XI, Corollaire 5.3 bis, in the
registered Gille–Polo provisional recomposition of December 2008,
`sga3-exposes-xi-xii-xiv-gille-polo-2008` (content SHA256
`dd37c114bfb569a0d39c1cce727a0d87a8d40abf545d13e0b1a2d886d03b7498`).
In the retained `Expo11.pdf`, one-based PDF pages 26–27, printed
pages 110–111, original pages 167–168, the surrounding hypotheses fix a
smooth affine group, and the corollary asserts closed smooth
representability of the normalizer of a multiplicative-type subgroup.
A closed field torus is a special case. The retained source folder is
`/home/taskhub/pilot/literature/Grothendieck - SGA 3 Exposes XI, XII and XIV (Gille-Polo provisional recomposition, December 2008)`.

Milne, *Algebraic Groups* (2017), Corollary 13.10, printed p.257,
one-based PDF p.273, independently gives smoothness of such normalizers.
The registered source is `milne-2017-algebraic-groups`, content SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The retained official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` contains no correction to
this corollary. The target's paired Markdown explains its full source
correspondence. The implemented proof uses direct normalizer lifting
and descent; Milne instead deduces normalizer smoothness from centralizer
smoothness through equality of identity components.

Worker 1630 wrote the generalization and descent argument; Worker 950's
published split normalizer proof supplies the adapted helper body.
