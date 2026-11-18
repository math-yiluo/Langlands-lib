# Nested standard Levis: rank drop, simple-root labels and nested transports

Module `Langlands.GroupScheme.Rational.StandardLeviNestedTransport`, namespace
`Langlands.GroupScheme.StandardLeviNested`.

## Purpose and provenance

This module is structural glue for an induction on semisimple rank over the
actual standard Levi subgroups of a connected reductive group. Waldspurger uses
such an induction in the proof of Proposition VI.3.1 (J.-L. Waldspurger, *La
formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), pp. 302–305). The induction applies the
proposition to proper standard Levi subgroups `M' = M_J` of `G`, where
`J ⊊ Δ`. Each such `M_J` is again connected reductive. Because `J` is a proper
subset of `Δ`, `M_J` has strictly smaller relative root rank than `G`.
Waldspurger invokes this strict rank drop explicitly in the proof (p. 304).

Standard Levis and standard parabolics of `M_J` behave differently. Fix
`K ⊆ J`.

- The standard Levi of `M_J` for `K` is identified with the ambient standard
  Levi `M_K` of `G`, which lies inside `M_J`.
- The standard parabolic of `M_J` for `K` is the preimage of the ambient `P_K`
  under `M_J → G`, that is `P_K ∩ M_J`. It is in general not a standard
  parabolic of `G`. For example, take `G = GL_3` with its upper triangular
  Borel `B` and `M_J = GL_2 × GL_1`. The standard Borel of `M_J` is `B ∩ M_J`.
  It omits the root group `U_{23}`, which lies in `B` and hence in every
  standard parabolic of `G`. So `B ∩ M_J` is not a standard parabolic of `G`.

The Lean statements use exactly these two forms: preimages for parabolic, Levi
and unipotent functors in the rank package, and isomorphisms over `G` for the
Levi schemes.

Provenance is **derived**. Apart from the strict rank drop, which Waldspurger
invokes explicitly on p. 304, he takes these facts for granted. No statement
here is quoted from the source. Every result is a short corollary of published
Library theorems:

- `BruhatTits.SpecialCompact.standardLevi_isConnectedReductive`;
- `Standard.isMaximalSplitTorus_leviTorusHom`;
- `standardLeviStandardFamilies` and `relativeSimpleRootBasis`;
- `standardCocharacter` and `standardLevi_mono_of_exists`;
- `Dynamic.centralizer_eq_comap_of_mono`;
- `SubgroupFunctor.IsRepresentedBy.comp`, `SubgroupFunctor.map_comap_of_le_range`
  and `IsRepresentedBy.isoOfIsRepresentedBy`;
- `rationalPointSubgroupHomeomorph` and `Aubert.General.dynamicCentralizerPointHomeomorph`.

The module introduces no new mathematical objects. It only names isomorphisms,
homeomorphisms and label bijections between objects that already exist.

## Conventions

- `k` is a field and `G` is an affine group scheme over `Spec k`.
- `i : T → G` is a maximal split torus, `ν` is a generic cocharacter and `Δ` is
  `simpleRelativeRoots i ν`.
- For `J ⊆ Δ`, `M_J` is the actual standard Levi scheme `Standard.leviScheme i ν J`,
  with closed immersion `Standard.leviHom i ν J : M_J → G`.
- `iL := Standard.leviTorusHom i ν J : T → M_J` is the torus of `M_J`.
- Point topologies are the Library's identity-test topology
  `rationalPointTopology` on affine schemes over `Spec R`, for a commutative ring
  `R` carrying a topology.
- A *multiplicative homeomorphism* (Lean `≃ₜ*`, `ContinuousMulEquiv`) is a group
  isomorphism that is also a homeomorphism. At this generality the point groups
  need not be topological groups: no continuity of multiplication or inversion
  is claimed. When `R` is a topological ring and the schemes are locally of
  finite type, the published `rationalPoint_isTopologicalGroup` makes the point
  groups topological groups, and these maps are then isomorphisms of
  topological groups.

Local instances, not exported, record standard facts:

- the point topology above (`nestedRationalPointTopology`);
- affineness of the dynamic centralizer scheme, a closed subgroup of an affine
  scheme (`nestedCentralizerAffine`);
- affineness of `M_J` over the base, from `Standard.isClosedSubgroup_leviHom`
  (`nestedLeviSchemeAffineHom`);
- affineness of `G` itself (`nestedAmbientAffine`).

## Generic nested represented subgroups

Let `j : L → G` be a monomorphism of group schemes over a scheme `S`, and `F` a
subgroup functor of `G` contained in the range of `j`. Let `E = j⁻¹F`, and let
`h : H → L` represent `E`.

- `isRepresentedBy_comp`: `h ≫ j` represents `F`.
- `nestedIso`: for any representative `h' : H' → G` of `F`, an isomorphism
  `H ≅ H'`.
- `nestedIso_hom_comp`: the isomorphism lies over `G`, i.e.
  `nestedIso.hom ≫ h' = h ≫ j`.

Over `S = Spec R`, with `R` a commutative ring carrying a topology, all schemes
affine, and `j`, `h`, `h'` closed subgroups:

- `nestedPointHomeomorph`: a multiplicative homeomorphism
  `H(R) ≃ₜ* H'(R)`.
- `nestedPointHomeomorph_apply_comp` and `nestedPointHomeomorph_apply`: it is
  `p ↦ p ≫ nestedIso.hom`, and it satisfies `φ(p) ≫ h' = p ≫ h ≫ j`.
- `nestedCarrierHomeomorph`: a multiplicative homeomorphism between the
  rational-point subgroups `E(R) ⊆ L(R)` and `F(R) ⊆ G(R)`, each with its subspace
  topology.
- `nestedCarrierHomeomorph_apply_coe`: this isomorphism is `x ↦ x ≫ j`.

## Nested dynamic centralizers

Let `j : L → G` be a monomorphism over `Spec R`, `χ : 𝔾_m → L`, and
`χ' : 𝔾_m → G` with `χ ≫ j = χ'`.

- `comap_centralizer`: `j⁻¹ Z_G(χ') = Z_L(χ)`.

Assume moreover that `Z_G(χ')` lies in the range of `j`.

- `isRepresentedBy_nestedCentralizerHom`: the centralizer inclusion of `χ` into
  `L`, followed by `j`, represents `Z_G(χ')`.
- `nestedCentralizerIso` and `nestedCentralizerIso_hom_comp`: the actual
  centralizer schemes `Dynamic.Affine.centralizerScheme χ` and
  `Dynamic.Affine.centralizerScheme χ'` are isomorphic over `G`.

When `j` is in addition a closed subgroup:

- `nestedCentralizerPointHomeomorph` and its `_apply` law: a multiplicative
  homeomorphism between the rational-point groups of the two centralizer
  schemes.
- `nestedLeviHomeomorph` and its `_apply_coe` law: `Z_L(χ)(R) ⊆ L(R)` and
  `Z_G(χ')(R) ⊆ G(R)`, with subspace topologies, correspond under the
  multiplicative homeomorphism `x ↦ x ≫ j`.
- `dynamicCentralizerPointHomeomorph_nested`: the two identifications commute with
  the published identifications `dynamicCentralizerPointHomeomorph` of scheme
  points with literal centralizer points.

## Actual standard Levis

From here on `G` is connected reductive (`hG`), `i` is maximal split (`hi`) and
`ν` is generic (`hν`).

### Rank drop

`leviScheme_rankPackage` packages the following facts for `J ⊆ Δ`:

- `M_J` is connected reductive;
- `iL` is a maximal split torus of `M_J`;
- `ν` is generic for `iL`;
- the simple relative roots of `iL` (for `ν`) are exactly `J`;
- `J` is finite;
- the relative root rank of `iL` is `Nat.card J`;
- for every `K ⊆ J`, the standard parabolic, Levi and unipotent subgroup functors
  of `iL` for `K` are the preimages under `M_J → G` of those of `i` for `K`.

Consequences:

- `simpleRelativeRoots_leviTorusHom`: the simple roots of `iL` are `J`.
- `relativeRootRank_leviTorusHom_lt`: if `J ⊊ Δ`, then
  `relativeRootRank iL < relativeRootRank i`. This is the strict rank drop used
  by the induction.
- `relativeRootRank_leviTorusHom_rootSet_lt`: the same for `J = rootSet i ν I`,
  where `I` is a `Finset` of simple-root labels that omits some label. This is
  the label format of the VI.3.1 target.

### Standard cocharacters and nested dynamic Levis

Let `K ⊆ J ⊆ Δ` and let `ζ` be a standard cocharacter of `i` for `K`.

- `isStandardCocharacter_leviTorusHom`: `ζ` is a standard cocharacter of `iL`
  for `K`.
- `centralizer_le_range_leviHom`: `Z_G(ζ)` lies in the range of `M_J → G`. This
  only needs `K ⊆ J`.
- `groupHom_comp_leviTorusHom_comp`: `(ζ ≫ iL) ≫ (M_J → G) = ζ ≫ i`. This holds
  for any `J` and `ζ`.
- `standardNestedCentralizerIso` and its `_hom_comp` law: the actual dynamic
  centralizer scheme of `ζ ≫ iL` in `M_J` is isomorphic over `G` to that of
  `ζ ≫ i` in `G`.

When `k` carries a topology (an arbitrary one; see the conventions on
multiplicative homeomorphisms):

- `standardNestedCentralizerPointHomeomorph` and its `_apply` law: a
  multiplicative homeomorphism between the rational-point groups of these two
  schemes.
- `standardNestedLeviHomeomorph` and its `_apply_coe` law: the literal Levi
  points of `ζ` in `M_J(k)` and in `G(k)`, with subspace topologies, correspond
  under the multiplicative homeomorphism given by the inclusion
  `M_J(k) → G(k)`.

### Nested standard Levi schemes

For `K ⊆ J ⊆ Δ`:

- `standardLevi_le_range_leviHom`: the standard Levi functor of `i` for `K` lies
  in the range of `M_J → G`.
- `comap_standardLevi_leviHom`: its preimage in `M_J` is the standard Levi functor
  of `iL` for `K`.
- `standardNestedLeviIso` and its `_hom_comp` law:
  `Standard.leviScheme iL ν K ≅ Standard.leviScheme i ν K` over `G`.

When `k` carries a topology (again arbitrary):

- `standardNestedLeviPointHomeomorph` and its `_apply` law: a multiplicative
  homeomorphism between the rational-point groups of these two schemes.
- `standardNestedLeviPointsHomeomorph` and its `_apply_coe` law:
  `standardLeviPoints iL ν K ⊆ M_J(k)` and `standardLeviPoints i ν K ⊆ G(k)`, with
  subspace topologies, correspond under the multiplicative homeomorphism given
  by the inclusion `M_J(k) → G(k)`.

### Simple-root labels

Labels are the Library's `SimpleRoot i ν`, a subtype of `Δ`, and `Finset`s of
labels, with `rootSet` giving the underlying set of characters. Fix `J ⊆ Δ`.

- `mem_of_mem_simpleRelativeRoots_leviTorusHom`: a simple root of `iL` lies in
  `J`.
- `leviSimpleRootEquiv`: an equivalence `SimpleRoot iL ν ≃ J` that keeps the
  character (`leviSimpleRootEquiv_apply_coe`).
- `ambientSimpleRoot`: an embedding `SimpleRoot iL ν ↪ SimpleRoot i ν` that keeps
  the character (`ambientSimpleRoot_coe`).
- `ambientLabels L`: the image of `L` under this embedding (`mem_ambientLabels`).
  - `rootSet_ambientLabels`: it names the same characters as `L`.
  - `rootSet_ambientLabels_subset`: these characters lie in `J`.
- `lowerLabels I`: the preimage of `I` under the embedding (`mem_lowerLabels`).
  - `rootSet_lowerLabels`: it names `rootSet i ν I ∩ J`.
  - `rootSet_lowerLabels_of_subset`: if `rootSet i ν I ⊆ J`, it names exactly
    `rootSet i ν I`.
- Round trips:
  - `ambientLabels_lowerLabels`: `ambientLabels (lowerLabels I) = I` when
    `rootSet i ν I ⊆ J`.
  - `lowerLabels_ambientLabels`: `lowerLabels (ambientLabels L) = L` always.

For the Levi `M_{I'}` with `J = rootSet i ν I'`:

- `leviRootLabelEquiv`: an equivalence between `SimpleRoot iL ν` and the labels in
  `I'`, keeping characters (`leviRootLabelEquiv_apply_coe`).
- `rootSet_lowerLabels_rootSet` and `ambientLabels_lowerLabels_rootSet`: the
  specializations of the two laws above to label sets `I ⊆ I'`.

## Scope

This module provides only the group-scheme, point-topology and label
identifications. It does not transport measures, representations, characters,
weights or wave packets between `M_J` and `G`; those analytic transports belong
to the eventual induction proof. Nothing here assumes or proves any part of
Proposition VI.3.1.
