# The standard Iwahori subgroup of `GL_N` and the hyperspecial `GL_N(𝒪)`

This module adds a regression example to the depth-zero `GL_N` data of
[`GeneralLinearDepthZero`](GeneralLinearDepthZero.md). For `N ≥ 2` it is the
comparison target for the Iwahori subgroup, which is not hyperspecial (see
Provenance); for `N ≤ 1` the construction gives back the hyperspecial pair.
Write `K = G^0(𝒪) = GL_N(𝒪[F])` for the integral points of the standard model
and `K^+ = G(F)^{0+}` for the kernel of reduction
`GL_N(𝒪[F]) → GL_N(𝓀[F])`.
These are the published `(generalLinearModelData F N).neutral.integralPoints`
and `(generalLinearQuotientData F N).positivePoints`.

- Every subgroup `H` of `GL_N(𝓀[F])` has a preimage in `K`, a subgroup of
  `G(F)`. The preimage of `⊤` is `K` and the preimage of `⊥` is `K^+`. Relative
  indices and normality of preimages are those of the subgroups of
  `GL_N(𝓀[F])`. Reduction identifies the preimage of `H` modulo `K^+` with
  `H`.
- The standard Iwahori subgroup `I` is the preimage of the upper triangular
  group `B(𝓀[F])`, and `I^+` is the preimage of the upper unipotent group
  `U(𝓀[F])`. In matrix terms, `I` consists of the invertible integral matrices
  whose strictly lower entries lie in the maximal ideal; `I^+` adds that the
  diagonal entries are `1` modulo the maximal ideal.
- `K^+ ≤ I^+ ≤ I ≤ K`, with `q = Nat.card 𝓀[F]`:
  - `[K : I] = [GL_N(𝓀[F]) : B(𝓀[F])]`, and
    `q^(N choose 2) (q - 1)^N [K : I] = ∏_{i < N} (q^N - q^i)`;
  - `[K : I] = q + 1` for `N = 2`;
  - `[I : I^+] = (q - 1)^N` and `[I^+ : K^+] = q^(N choose 2)`.
- `I^+` and `K^+` are normal in `I`, and `I/I^+` is isomorphic to the diagonal
  torus `(GL_1(𝓀[F]))^N`, the Levi factor of the singleton block shape.
- For `N ≥ 2`, `I` is a proper subgroup of `K`. For `N ≤ 1` every invertible
  matrix is upper triangular and the only upper unipotent matrix is `1`, so
  `I = K` and `I^+ = K^+`.

The finite-field counts behind these indices are proved for the singleton
block shape of the Library's `Langlands.GeneralLinear.BlockShape` API.

## Provenance

The module is derived. Its statements are standard facts about `GL_N` over a
discrete valuation ring with finite residue field, obtained here from
published Library results and Mathlib. The task objective (Task 3557) asks for
proved regression examples in its "Regression examples" section; this unit
compares the hyperspecial pair `K^+ ⊆ K` with the standard Iwahori pair
`I^+ ⊆ I`. For `N ≥ 2` the standard chamber is not a hyperspecial vertex, and
the KP comparison targets below concern a parahoric that is not hyperspecial;
the Lean proves only that `I` is then a proper subgroup of `K`
(`generalLinearIwahoriPoints_lt_integralPoints`). For `N = 1` (and the
degenerate `N = 0`) the definitions are still valid but give `I = K` and
`I^+ = K^+` (`generalLinearIwahoriPoints_of_le_one`,
`generalLinearIwahoriPositivePoints_of_le_one`), so they do not give a
non-hyperspecial example there.

The comparison values come from Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023). The registered original is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

- §3.1 (printed p. 142 / PDF p. 173), for `SL_2`: for `0 < x < 1/2` the
  bounded open subgroup `P_x` is the intersection of `P_0` and `P_{1/2}` and is
  given by matrices `[[o, o], [m, o]]`; "It is called an Iwahori subgroup".
  The matrix description of `I` in `mem_generalLinearIwahoriPoints` is the
  same lower-left condition, for `GL_N` and all strictly lower entries.
- Example 4.2.16 (printed p. 174 / PDF p. 205): the standard Iwahori subgroup
  of `PGL_2(k)` is "the preimage in `PGL_2(o)` of the upper triangular Borel
  subgroup in `PGL_2(f)`". The definition `generalLinearIwahoriPoints` is this
  construction for `GL_N`.
- Theorem 8.4.19(3) (printed p. 309 / PDF p. 340): for facets `F ≺ F'`, the
  preimage of the parabolic subgroup `p_F(F')` under the surjective map
  `G_F^0(O) → \bar G_F^0(f̄)` equals `G_{F'}^0(O)`. Here `O` and `f̄` are the
  valuation ring and residue field of the maximal unramified extension `K` of
  `k` (opening of §8.4, printed p. 302 / PDF p. 333), not of `k`. For `GL_N`,
  `F` the standard hyperspecial vertex and `F'` the standard chamber, this is
  the shape of `generalLinearIwahoriPoints`: a parahoric is the preimage of a
  parabolic of the special fibre. The Lean statements are over `F` itself,
  with its finite residue field.
- Theorem 8.4.10(2) (printed p. 305 / PDF p. 336): the root system of the
  maximal reductive quotient `\bar G_Ω` of the special fibre of `G_Ω^0` is
  `Φ_Ω`, the image of the affine roots vanishing on `Ω` (8.4.6). For the
  standard chamber of split `GL_N` no affine root vanishes, so this quotient
  is the special fibre of the split diagonal torus.
- 13.2.6 (printed p. 470 / PDF p. 501) identifies `P_{x,0}/P_{x,0+}` with the
  `f`-points of the maximal reductive quotient of the special fibre of the
  parahoric group scheme. For the standard hyperspecial vertex of `GL_N` this
  is `GL_N(𝓀[F])`, which gives the published `K/K^+`. For the barycentre of
  the standard chamber, by the previous item, it is the diagonal torus
  `(𝓀[F]^×)^N`, which is the value of `generalLinearIwahoriQuotientEquiv`.

The authors' corrections of 1 November 2024
(`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`) do not
amend any of these items.

- In Chapter 3 (PDF p. 26) they complete an unfinished sentence on p. 142
  before Notation 3.1.1: the unique maximal bounded subgroup of `T(k)` "is
  denoted `T(k)_0`". The Iwahori description on that page is unchanged.
- In Chapter 8 (PDF pp. 37–38) they replace the first sentences of §8.3 and
  §8.4, which now assume a perfect residue field; a finite residue field is
  perfect. They replace `o` with `O` twice in the second paragraph of §8.4.
  Just before Proposition 8.4.15 they insert the definition of the
  homomorphisms `ρ_{Ω,Ω'}` and the induced maps of special fibres, and they
  delete the first sentence of 8.4.15. They also amend Lemma 8.1.4,
  Remark 8.3.4, 8.3.6, the proof of Theorem 8.3.13, 8.4.2 and Lemma 8.4.4.
  Theorems 8.4.10 and 8.4.19 are not amended.
- In Chapter 13 (PDF p. 49) they amend 13.5.2, 13.6.2 and 13.8.5, not 13.2.6.

KP's objects are not used in the Lean statements. The module works with the
Library's `integralPoints`, `positivePoints`, the explicit preimages defined
here and the Library's concrete block-shape subgroups of `GL_N(𝓀[F])`. The KP
values above are what these results are compared against. The order of
`GL_N(𝔽_q)` is Mathlib's `Matrix.card_GL_field`.

## Setting

The local-field part is stated for a field `F` in universe `u` with
`ValuativeRel F`, `TopologicalSpace F` and `IsNonarchimedeanLocalField F`, and
for `N : ℕ`. `𝒪[F]` is its valuation ring and `𝓀[F]` its residue field. Points
of `G = GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)` are read as
matrices through the published `GeneralLinear.rationalPointsEquiv N _`.

The finite-field part is in namespace `Langlands.GeneralLinear.BlockShape`,
for `n : ℕ`, a finite field `K` and, where stated, an arbitrary commutative
ring `R`. It uses the published singleton shape `singletons n` (`n` blocks of
size `1`) and its `parabolic`, `unipotentRadical`, `unipotentSubgroup`, `Levi`,
`leviProjection` and `decomposition`. By the published
`singletons_mem_parabolic_iff` and `singletons_unipotentSubgroup`, its
parabolic is the upper triangular group and its unipotent subgroup is the
upper unipotent group.

The file sets `backward.isDefEq.respectTransparency` and
`backward.isDefEq.respectTransparency.types` to `false`, as does the imported
`GeneralLinearDepthZero`.

## Declarations

### Reduction preimages

These are in namespace `Langlands.BruhatTits.IntegralModels`.

- `glResidueMap F N` (abbreviation): `Matrix.GeneralLinearGroup.map
  (IsLocalRing.residue 𝒪[F])`, reduction `GL (Fin N) 𝒪[F] →* GL (Fin N) 𝓀[F]`.
- `glIntegralInclusion F N` (abbreviation): `Matrix.GeneralLinearGroup.map
  (algebraMap 𝒪[F] F)`, the inclusion `GL (Fin N) 𝒪[F] →* GL (Fin N) F`.
- `glIntegralInclusion_injective`: it is injective (`𝒪[F] → F` is injective).
- `glResidueMap_surjective`: reduction is surjective. The proof applies the
  published smooth Henselian lifting `IntegralModel.reduction_surjective` to
  the neutral model of `generalLinearModelData F N`, using
  `GeneralLinear.standardIntegralModel_isSmooth` and
  `henselianLocalRing_integer`, and transfers along the published
  `generalLinearSpecialFibrePointsEquiv` and its reduction formula.
- `generalLinearReductionPreimage F N H` (definition): for
  `H : Subgroup (GL (Fin N) 𝓀[F])`, the subgroup of `rationalPoints G` whose
  matrices are `glIntegralInclusion F N u` for some `u` with
  `glResidueMap F N u ∈ H`. It is the comap along `rationalPointsEquiv` of the
  image under `glIntegralInclusion` of `H.comap (glResidueMap F N)`.
- `mem_generalLinearReductionPreimage`: the membership criterion just stated.
- `mem_generalLinearReductionPreimage_of_eq`: if the matrix of `g` is
  `glIntegralInclusion F N u`, then `g` is in the preimage of `H` exactly when
  `glResidueMap F N u ∈ H`.
- `generalLinearReductionPreimage_mono`: `H ≤ H'` implies the same for the
  preimages.
- `generalLinearReductionPreimage_top`: the preimage of `⊤` is
  `(generalLinearModelData F N).neutral.integralPoints`, by the published
  `mem_generalLinear_integralPoints`.
- `generalLinearReductionPreimage_bot`: the preimage of `⊥` is
  `(generalLinearQuotientData F N).positivePoints`, by the published
  `mem_generalLinear_positivePoints`.
- `generalLinearReductionPreimage_relIndex`: the relative index of the
  preimage of `H` in the preimage of `H'` is `H.relIndex H'`. The proof uses
  Mathlib's `Subgroup.relIndex_comap`,
  `Subgroup.relIndex_map_map_of_injective` and surjectivity of reduction.
- `generalLinearReductionPreimage_normal`: if `H.subgroupOf H'` is normal, so
  is the preimage of `H` in the preimage of `H'`.
- `positivePoints_subgroupOf_generalLinearReductionPreimage_normal`
  (instance): `K^+` is normal in every preimage.
- `generalLinearReductionPreimageResidue F N H` (definition): the group
  homomorphism from the preimage of `H` to `H` that sends a point to the
  reduction of its integral matrix.
- `generalLinearReductionPreimageResidue_apply`: if the matrix of `g` is
  `glIntegralInclusion F N u`, its image is `glResidueMap F N u`.
- `generalLinearReductionPreimageResidue_surjective`: it is surjective.
- `generalLinearReductionPreimageResidue_ker`: its kernel is
  `K^+.subgroupOf` the preimage of `H`.
- `generalLinearReductionPreimageQuotientEquiv F N H` (definition): the group
  isomorphism from the preimage of `H` modulo `K^+` to `H`, by Mathlib's first
  isomorphism theorem.
- `glResidueMap_apply`: the `(i, j)` entry of the reduction of `u` is the
  residue of the `(i, j)` entry of `u`.
- `glResidueMap_isUpperTriangular_iff`: the reduction of `u` is upper
  triangular exactly when every entry `u i j` with `j < i` lies in the maximal
  ideal.
- `glResidueMap_apply_eq_one_iff`: the `(i, i)` entry of the reduction is `1`
  exactly when `u i i - 1` lies in the maximal ideal.

### The singleton shape over a finite field

These are in namespace `Langlands.GeneralLinear.BlockShape`.

- `card_generalLinear_one_of_finite`: `Nat.card (GeneralLinear 1 K) =
  Nat.card K - 1`, by `Matrix.card_GL_field`.
- `card_singletons_levi`: the Levi factor `(singletons n).Levi K`, `n` copies of
  `GL_1`, has `(Nat.card K - 1)^n` elements.
- `card_singletons_unipotentRadical`: for any commutative ring `R`,
  `Nat.card ((singletons n).unipotentRadical R) = Nat.card R ^ n.choose 2`, as
  natural-number cardinalities (for infinite `R` and `n ≥ 2` both sides are
  `0`). The proof uses the published coordinates `radicalCoordinates`: one
  entry for each pair `i < j`.
- `card_singletons_parabolic`: the upper triangular group over `K` has
  `Nat.card K ^ n.choose 2 * (Nat.card K - 1)^n` elements, through the
  published factorization `decomposition` (`g = u m`).
- `index_singletons_unipotentRadical`: the radical has index
  `(Nat.card K - 1)^n` in the upper triangular group; it is the kernel of the
  surjective `leviProjection` (surjective by the published
  `leviProjection_section`).
- `singletons_unipotentSubgroup_subgroupOf`: for any commutative ring `R`,
  `unipotentSubgroup` viewed inside `parabolic` is `unipotentRadical`.
- `singletons_unipotentSubgroup_le`: `unipotentSubgroup R ≤ parabolic R`.
- `card_singletons_unipotentSubgroup`: `Nat.card ((singletons n).unipotentSubgroup
  R) = Nat.card R ^ n.choose 2` for any commutative ring `R`.

### The standard Iwahori subgroup

These are in namespace `Langlands.BruhatTits.IntegralModels`. Here
`B = (singletons N).parabolic 𝓀[F]` and
`U = (singletons N).unipotentSubgroup 𝓀[F]`.

- `generalLinearIwahoriPoints F N` (definition): `I`, the preimage of `B`.
- `generalLinearIwahoriPositivePoints F N` (definition): `I^+`, the preimage of
  `U`.
- `mem_generalLinearIwahoriPoints`: `g ∈ I` exactly when its matrix is
  `glIntegralInclusion F N u` for some `u : GL (Fin N) 𝒪[F]` whose entries
  `u i j` with `j < i` lie in the maximal ideal.
- `mem_generalLinearIwahoriPositivePoints`: `g ∈ I^+` exactly when, moreover,
  every `u i i - 1` lies in the maximal ideal.
- `generalLinearIwahoriPositivePoints_le`: `I^+ ≤ I`.
- `positivePoints_le_generalLinearIwahoriPositivePoints`: `K^+ ≤ I^+`.
- `generalLinearIwahoriPoints_le_integralPoints`: `I ≤ K`.
- `generalLinearIwahoriPoints_relIndex`: `I.relIndex K = B.index`.
- `generalLinearIwahoriPositivePoints_relIndex`: `I^+.relIndex I =
  (Nat.card 𝓀[F] - 1)^N`.
- `positivePoints_relIndex_generalLinearIwahoriPositivePoints`:
  `K^+.relIndex I^+ = Nat.card 𝓀[F] ^ N.choose 2`.
- `generalLinearIwahoriPoints_relIndex_mul`: with `q = Nat.card 𝓀[F]`,
  `q ^ N.choose 2 * (q - 1)^N * I.relIndex K =
  ∏ i : Fin N, (q ^ N - q ^ (i : ℕ))`. The proof combines
  `card_singletons_parabolic`, Mathlib's `Subgroup.card_mul_index` and
  `Matrix.card_GL_field`.
- `generalLinearIwahoriPoints_relIndex_two`: for `N = 2`,
  `I.relIndex K = Nat.card 𝓀[F] + 1`. The proof cancels the nonzero factor
  `q (q - 1)^2` in the order formula, using `1 < q`.
- `generalLinearIwahoriPoints_of_le_one`: for `N ≤ 1`, `I = K`. With at most
  one index there is no pair `j < i`, so `B = ⊤`, and the preimage of `⊤` is
  `K`.
- `generalLinearIwahoriPositivePoints_of_le_one`: for `N ≤ 1`, `I^+ = K^+`.
  An upper unipotent matrix of size at most one is `1`, so `U = ⊥`, and the
  preimage of `⊥` is `K^+`.
- `generalLinearIwahoriPoints_lt_integralPoints`: for `2 ≤ N`, `I < K`. The
  published `Langlands.GeneralLinear.transvectionUnit` at the pair `(1, 0)`
  with parameter `1` is an invertible matrix over `𝓀[F]` that is not upper
  triangular, so `B ≠ ⊤`. If `I = K`, then `B.index = K.relIndex K = 1`, which
  forces `B = ⊤`.
- `generalLinearIwahoriPositivePoints_normal`: `I^+.subgroupOf I` is normal,
  since the radical is normal in `B`.
- `generalLinearIwahoriPositivePoints_subgroupOf_normal` (instance): the same,
  as an instance.
- `positivePoints_normal_generalLinearIwahoriPoints`: `K^+.subgroupOf I` is
  normal.
- `generalLinearIwahoriDiagonal F N` (definition): the homomorphism
  `I →* (singletons N).Levi 𝓀[F]` that reduces and then takes the diagonal
  (`leviProjection` after `generalLinearReductionPreimageResidue`).
- `generalLinearIwahoriDiagonal_surjective`: it is surjective.
- `generalLinearIwahoriDiagonal_ker`: its kernel is `I^+.subgroupOf I`.
- `generalLinearIwahoriQuotientEquiv F N` (definition): the group isomorphism
  `I ⧸ I^+.subgroupOf I ≃* (singletons N).Levi 𝓀[F]`.

## Scope

No building, facet or point `x` appears. Nothing here identifies `I` or `I^+`
with KP's `G(k)^0_C` or `P_{x,0}`, `P_{x,0+}` for the barycentre `x` of the
standard chamber, or `K`, `K^+` with `P_{x,0}`, `P_{x,0+}` for the standard
hyperspecial vertex. Theorems 8.4.10(2) and 8.4.19(3) and 13.2.6 are
comparison targets, not proved statements: no parahoric group scheme for the
chamber is constructed, and no reductive quotient of its special fibre. Nor is `I`
shown to satisfy the Library's abstract notions
`KPParahoric.IsIwahoriSubgroup` or `ChamberIwahori.chamberIwahori`, or to be
an instance of `BlockIwahoriDefinitions`' `iwahoriLower`, `iwahoriLevi` and
`iwahoriUpper`. `I` and `I^+` are not shown to be open or compact, and `I^+` is
not shown to be pro-`p`. Only the standard lattice and the standard chamber
are treated: other chambers and other parahorics (preimages of other standard
parabolics are available through `generalLinearReductionPreimage`, but their
indices are not computed), `SL_N` and other forms are not covered.
