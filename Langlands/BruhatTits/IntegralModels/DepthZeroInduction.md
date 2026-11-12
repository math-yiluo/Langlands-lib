# Depth-zero inflation and compact induction for supplied KP models

This module is the representation-theoretic consumer test of the depth-zero
reduction in `Langlands.BruhatTits.IntegralModels.DepthZeroReduction`. That
module formalizes, for supplied data, Kaletha–Prasad, *Bruhat–Tits Theory: A
New Approach* (2023), 13.2.6 (printed p. 470 / PDF p. 501): the identification
`P_{x,0}/P_{x,0+} ≅ \bar G_x(f)`. Here a representation of `\bar G_x(f)` is
inflated to `G^0(R)` and compactly induced to the generic group. The module
then proves the resulting Frobenius reciprocity with kernel invariants. The
registered original is `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
KP do not state these representation-theoretic constructions. They are
internal, built from the published reduction map, Mathlib's invariants of a
normal subgroup, and the Library's compact induction from an open subgroup
(`Langlands.Representation.Induction.OpenAdjunction`). No model, radical,
quotient or topology existence assertion is made.

## Setting and notation

As in `DepthZeroReduction`, `R` is a domain with fraction field `K`, and `G`
is a group scheme over `Spec K`. The data are
`D : RelativeComponentModelData R K G` and `Q : SpecialFibreQuotientData D`.
Write `H = D.neutral.integralPoints`, the subgroup `G^0(R)` of `G(K)`, and
`N = Q.parahoricReduction.ker`. By `ker_parahoricReduction`, `N` is
`G(K)^{0+} ∩ G^0(R)` when the projection is the represented fppf quotient. The
coefficient ring `k` is an arbitrary commutative ring in any universe.
Representation spaces `V` and `W` lie in the universe `u` of `R` and `K`, as
the Library's compact induction functor requires. As before, `hrad` and `hQ`
are the first two conjuncts of `Q.IsReductiveQuotient`.

## Declarations

Over a local domain:

- `inflation σ` is `σ.comp Q.parahoricReduction`. It is the inflation to `H`
  of a representation `σ` of `rationalPoints Q.quotient = \bar G(f)`.
  `inflation_apply` evaluates it.
- `congruenceSubgroup_subgroupOf_le_ker` states that the level-one congruence
  subgroup of the neutral model, inside `H`, lies in `N`. A section that
  reduces to the identity has identity image in the quotient. Neither `hrad`
  nor `hQ` is needed.
- `inflation_ker_apply` states that elements of `N` act trivially on an
  inflation.

Over a Henselian local domain with perfect residue field:

- `depthZeroQuotientEquiv_symm_parahoricReduction` states that the inverse of
  `depthZeroQuotientEquiv hrad hQ` sends `parahoricReduction g` to the coset of
  `g`.
- `kernelInvariants hrad hQ ρ` is a representation of `\bar G(f)` on the
  `N`-invariants of a representation `ρ` of `H`. It is Mathlib's
  `Representation.quotientToInvariants ρ N`, a representation of `H ⧸ N`,
  composed with the inverse of `depthZeroQuotientEquiv`.
  `kernelInvariants_parahoricReduction_apply` states that
  `parahoricReduction g` acts on the invariants as `ρ g`.
- `inflationHomEquiv hrad hQ σ ρ` is a bijection from `H`-intertwining maps
  `inflation σ → ρ` to `\bar G(f)`-intertwining maps `σ → kernelInvariants ρ`.
  Forward, an intertwining map lands in the `N`-invariants because `N` acts
  trivially on the inflation. It is `\bar G(f)`-equivariant because every
  element of `\bar G(f)` is a reduction, by `parahoricReduction_surjective`.
  Backward, an intertwining map is composed with the invariant-subspace
  inclusion. Both round trips are definitional.

For an arbitrary topological-group structure on `rationalPoints G` and a local
domain base, assuming
`hC : IsOpen (D.neutral.congruenceSubgroup : Set (rationalPoints G))`:

- `isOpen_ker_parahoricReduction hC` states that `N` is open in `H` with the
  subspace topology. `N` contains the preimage of the open congruence subgroup.
  A subgroup containing an open subgroup is open.
- `kerOpenSubgroup hC` is `N` as an open subgroup of `H`.
- `isSmooth_inflation hC σ` states that every inflation is smooth in the
  Library sense: each vector is fixed by the open subgroup `N`. No topology
  is used on `\bar G(f)` or on the representation space.
- `inflationSmoothRep hC σ` bundles the inflation as a smooth representation
  of `H`. `depthZeroInduction hC σ` is its image under the Library's
  `Induction.smoothCompactInduction k H`. This is the smooth representation
  `c-Ind_{G^0(R)}^{G(K)} infl σ` of `G(K)`.

Over a Henselian local domain with perfect residue field, with the same
topological assumptions:

- `depthZeroInductionHomEquiv hrad hQ hH hC σ B` additionally assumes
  `hH : IsOpen (H : Set (rationalPoints G))`. For every smooth representation
  `B` of `G(K)`, it gives a bijection from morphisms
  `depthZeroInduction hC σ ⟶ B` to `\bar G(f)`-intertwining maps from `σ` to
  `kernelInvariants hrad hQ` of the restriction of `B` to `H`. This is
  `Hom_{G(K)}(c-Ind infl σ, π) ≃ Hom_{\bar G(f)}(σ, π^N)`. It composes the
  Library's Frobenius reciprocity `Induction.compactInductionHomEquiv H hH`
  with the identification of smooth-category morphisms with intertwining maps
  and with `inflationHomEquiv`.

## Nonarchimedean local fields

For a nonarchimedean local field `F` (Mathlib's `IsNonarchimedeanLocalField`),
the base is the valuation ring `𝒪[F]`:

- `henselianLocalRing_integer` proves that `𝒪[F]` is a Henselian local ring.
  It uses Mathlib's `I`-adic completeness of `𝒪[F]` and the Henselian
  property of adically complete rings, stated for a uniform structure
  compatible with the topology of `F`. The residue field `𝓀[F]` is finite, so
  Mathlib's `PerfectField.ofFinite` makes it perfect.
- `isOpen_integralPoints_of_congruenceBasis` and
  `isOpen_congruenceSubgroup_of_congruenceBasis` assume the published
  `LocalFieldIntegralModel.CongruenceNeighborhoodBasisStatement`, which has no
  proof yet. Under it, for an affine `G` and `D` over `𝒪[F]`, `G^0(𝒪[F])` and
  its level-one congruence subgroup are open in `rationalPoints G`. Here
  `rationalPoints G` has the canonical topology `rationalPointTopology F G.X`.
  The second uses `congruenceSubgroupAt_one`.
- `localFieldDepthZeroInductionHomEquiv` additionally assumes that the
  structure morphism of `G` is locally of finite type, so that
  `rationalPoint_isTopologicalGroup` applies. It specializes
  `depthZeroInductionHomEquiv` to this topology, with the openness
  hypotheses supplied by the congruence-basis statement.

The conclusions are therefore conditional on
`CongruenceNeighborhoodBasisStatement`, and on supplied `D`, `Q`, `hrad` and
`hQ`. No identification of `D.neutral` with a Bruhat–Tits parahoric group
scheme is made. Neither is the Moy–Prasad identification of `N` (KP
Corollary 8.4.12, printed p. 306 / PDF p. 337). Admissibility, irreducibility
and the theory of depth-zero types are not treated here.
