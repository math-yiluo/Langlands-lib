# Actual archimedean Iwasawa existence compatible with a rational Levi: proof

Author: Worker 4320.

`Langlands.Global.InfinitePlaceGroupPoints.leviCompatibleIwasawaStatement`
proves exactly the published proposition
`Langlands.Global.InfinitePlaceGroupPoints.LeviCompatibleIwasawaStatement.{u}`
of [`InfinitePlaceLeviIwasawaStatement`](InfinitePlaceLeviIwasawaStatement.md),
at arbitrary universe `u` and with no added premise. The statement and its
imported definitions are unchanged.

Fix a number field `F : Type u`, an actual group scheme `G/F` with
`IsConnectedReductive G`, an actual parabolic inclusion `p : P ⟶ G` with
`IsParabolicSubgroup p`, a specified Levi inclusion `l : M ⟶ P` with
`IsRationalLeviSubgroup l`, and an infinite place `v`. The theorem constructs a
subgroup `K` of the existing group `InfinitePlaceGroupPoints F G v` that
satisfies all four clauses of `IsLeviCompatibleIwasawaCompact`:

1. `K` is compact and maximal among compact subgroups of `G(F_v)`.
2. `range(P(F_v) → G(F_v)) * K = G(F_v)`, with the parabolic image on the left.
3. `range(P(F_v) → G(F_v)) ∩ K = range(M(F_v) → G(F_v)) ∩ K`, where the
   second map is induced by the actual composite `l ≫ p`.
4. `K.comap (M(F_v) → G(F_v))` is compact and maximal among compact subgroups
   of the actual group `M(F_v)`.

The point carriers are the actual affine-test scheme points over
`v.Completion`, with the group-object law and the existing regular-function
evaluation topologies on `G(F_v)` and `M(F_v)`. The point maps are the existing
`affinePointsTarget` homomorphisms. The proof supplies no compact subgroup,
Iwasawa decomposition, Lie-group realization or point-topology identification
as a hypothesis. Splitness, isotropy and rank positivity are not assumed, so
non-split and anisotropic groups and the improper parabolic `P = G` are
included.

## Declarations

Both declarations are in namespace `Langlands.Global.InfinitePlaceGroupPoints`.

- `exists_leviCompatibleIwasawaCompact F G hG P p hp M l hl v`: the existence
  of `K` for one pair at one place.
- `leviCompatibleIwasawaStatement : LeviCompatibleIwasawaStatement.{u}`: the
  closing theorem. It introduces every quantified variable and premise of the
  published proposition and applies the existence theorem.

## Implemented proof

The existence theorem applies the published conditional result
`exists_leviCompatibleIwasawaCompact_of_dynamic` of
[`InfinitePlaceLeviIwasawaDynamic`](InfinitePlaceLeviIwasawaDynamic.md)
(Worker 1655). That theorem has two universal premises at the same universe
`u`. Both are discharged by published proofs:

- `ParabolicDynamicStatement.{u}` is the published theorem
  `Langlands.GroupScheme.parabolicDynamic` of
  [`Absolute.ParabolicDynamicProof`](../GroupScheme/Absolute/ParabolicDynamicProof.md)
  (Worker 3813 with Worker 4153). Over any field, a closed subgroup of a
  connected reductive group is parabolic exactly when its range is the dynamic
  parabolic `P(χ)` of a cocharacter `χ` defined over that field.
- `DynamicGeometricUnipotentRadicalStatement.{u}` is the published theorem
  `Langlands.GroupScheme.dynamicGeometricUnipotentRadical` of
  [`Dynamic.GeometricUnipotentRadicalProof`](../GroupScheme/Dynamic/GeometricUnipotentRadicalProof.md)
  (Worker 1281). Any representative of the identity-limit subgroup `U(χ)` is
  the geometric unipotent radical of the represented `P(χ)`.

With both premises supplied, the remaining argument is the published chain
below. This module adds no further mathematics.

1. **A common cocharacter over `F`.**
   [`InfinitePlaceLeviIwasawaAssembly`](InfinitePlaceLeviIwasawaAssembly.md)
   applies `DynamicLeviConjugacy.exists_cocharacter_parabolic_levi` over the
   original number field `F`, using the two premises above. It obtains one
   cocharacter `χ : 𝔾_m → G` over `F` such that `P(χ)` is the range of `p` and
   the dynamic centralizer of `χ` is the range of `l ≫ p`, on all test schemes.
   No minimal parabolic is chosen, so no claim that a minimal parabolic over
   `F` remains minimal over `F_v` is used.
2. **Base change to the completion.** The cocharacter and both representation
   certificates are base changed along `F → v.Completion` with
   `parabolic_baseChange`, `centralizer_baseChange` and functoriality of base
   change. Connected reductivity of the pullback of `G` comes from the
   published connected-reductive field-extension theorem.
3. **Analytic structure and closed star realization.** The published
   `NumberField.InfinitePlace.completion_isRCLikeNormedField` and
   `IsRCLikeNormedField.rclike` install an `RCLike` structure on
   `v.Completion` that keeps its normed field structure and topology. The
   published theorem
   `SelfAdjointRealization.connectedReductiveSelfAdjointRealizationStatement`
   gives a closed matrix representation of the pulled-back `G` whose
   rational-point image is stable under conjugate transpose. The real/complex
   conjugation construction
   `MatrixRepresentation.HasClosedStarRealization.hasRCLikeDiagonalStarLeviRealization`
   of `Dynamic.RCLikeLeviIwasawa` gives compatible diagonal realization data
   for the base-changed `p` and `l ≫ p`. This discharges
   `HasCompletionDiagonalStarLeviRealization F G P p M l v`
   (`completion_realization_of_dynamic`).
4. **Construction of the compact.** On the completion pullback,
   `Dynamic.LeviCompatiblePolarIwasawa` takes `K` to be the inverse image of
   the unitary matrix subgroup. Its affine polar construction proves that `K`
   is compact and maximal among compact subgroups. Polar factorization and the
   diagonal dynamic covering theorem give the ordered product with the
   parabolic image. The unitary intersection identity gives clause 3. The
   representation restricted along the closed Levi immersion has a polar
   construction of its own, which gives clause 4 for the comap of `K`.
5. **Transport to the original point groups.**
   [`InfinitePlaceLeviIwasawaRealization`](InfinitePlaceLeviIwasawaRealization.md)
   (`exists_leviCompatibleIwasawaCompact_of_completion_realization`) moves all
   four conclusions to `InfinitePlaceGroupPoints F G v` through the existing
   completion base-change equivalence. It uses multiplicative homeomorphisms
   of both the ambient and the Levi point carriers in their evaluation
   topologies. Affineness of `G` and `M` comes from their connected
   reductivity. The Levi map is the one induced by the original composite
   `l ≫ p`, and clause 4 keeps the `K.comap` formulation.

The closing theorem uses no hypothesis beyond those of the published
proposition. Each structural input named above is a published theorem, not a
premise. The only axioms used are `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance and scope

This is an internal composition of published Library results; it adds no
assertion from the literature. The proved proposition is the single-pair
specialization of Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Appendix B, Theorem B.4.1, printed p.547 (one-based
PDF p.552), registered as `getz-hahn-2024-automorphic-representations`. The
statement's Markdown records that specialization. The implemented route
differs from the source: it does not use Lie-theoretic Iwasawa decomposition,
conjugacy of maximal compact subgroups or Harish-Chandra's compatible Levi
choice. It instead uses a common rational cocharacter for the supplied pair, a
self-adjoint closed realization and the polar decomposition of matrices.

The theorem proves one pair at one place. It does not provide a simultaneous
compact choice across parabolics, existence of rational Levis for every
parabolic, nonarchimedean compacts, almost-everywhere integral compatibility,
adelic assembly, Siegel coverage or finite volume.
