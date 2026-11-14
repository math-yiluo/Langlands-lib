# Composition of actual standard integrals with a common Levi (target)

Worker 5. The module
`Langlands.Representation.Plancherel.DynamicCommonLeviComposition`
(namespace `Langlands.Plancherel.DynamicCommonLeviComposition`) states two
Prop-valued targets:

- `DistanceAdditiveRadicalFactorizationStatement`, a structural target: the
  ordered product decomposition of three actual dynamic radicals with a
  common Levi under the distance condition;
- `ConditionalDynamicCommonLeviCompositionStatement`, the main target:
  Waldspurger's composition formula IV.1 (12),
  `J_{P₂|P₀} = J_{P₂|P₁} J_{P₁|P₀}`, for the actual standard integrals of
  three dynamic parabolics with a common Levi. It takes the structural
  target as a hypothesis.

Neither target is proved here. The module defines the standard integral
between two dynamic parabolics with a common Levi, and the distance
condition. It proves the facts that these definitions need, and that the
new integral is the published opposite integral `J_{P̄|P}` when `P' = P̄`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082, registered as `waldspurger-2003-plancherel`, PDF
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

- I.1, printed p.240 / PDF p.6: a maximal compact subgroup `K` of `G` is
  fixed. It is the fixer of a special point of the apartment of `A₀`. Every
  closed algebraic subgroup `H` of `G` carries the left Haar measure with
  `mes(H ∩ K) = 1`.
- IV.1, printed p.278 / PDF p.44: for `P = MU`, `P' = MU' ∈ P(M)`,
  `(J_{P'|P}(π) f)(g) = ∫_{U ∩ U' \ U'} f(u'g) du'`, when the integrals,
  paired with vectors of the contragredient, converge absolutely ("défini
  par des intégrales convergentes").
- IV.1, proof of Theorem IV.1.1, printed p.279 / PDF p.45: the distance
  `d(P₁, P₂) = ♯(Σ^red(P₁) ∩ Σ^red(P̄₂))`. When
  `d(P', P'') = 1` and `d(P'', P) = d(P', P) − 1` the proof uses the product
  decomposition `U' ∩ Ū = (U'' ∩ Ū)(U' ∩ Ū'')` and Fubini.
- IV.1 (12), printed p.283 / PDF p.49: "Si `P'' ∈ P(M)` vérifie
  `d(P', P) = d(P', P'') + d(P'', P)`, alors
  `J_{P'|P}(π) = J_{P'|P''}(π) J_{P''|P}(π)`. Cela a été prouvé au cours de
  la démonstration du théorème."

The module writes `P₀ = P`, `P₁ = P''` and `P₂ = P'`. The condition reads
`d(P₂, P₀) = d(P₂, P₁) + d(P₁, P₀)` and the formula reads
`J_{P₂|P₀} = J_{P₂|P₁} J_{P₁|P₀}`.

## Provenance

The targets adapt IV.1 (12) to the Library's data. The following choices
are internal and are not in the source.

**Dynamic parabolics.** A parabolic of the Library is `P_G(ψ)` for a
cocharacter `ψ`, with radical `U_G(ψ)` and Levi `Z_G(ψ)`. The set `P(M)` is
represented by cocharacters `ψ` with the same centralizer subgroup functor
as a base cocharacter `χ`. All their parabolics then contain the literal
Levi `M = Z_G(χ)(F)`. Different cocharacters may give the same parabolic.

**Group form of the distance condition.** The module states the distance
condition with subgroups, not with reduced roots. `IsDistanceAdditive ψ₀ ψ₁ ψ₂`
is: `U₀ ∩ U₂ ≤ U₁` and `Ū₀ ∩ Ū₂ ≤ Ū₁`,
where `Uᵢ = U_G(ψᵢ)(F)` and `Ūᵢ = U_G(ψᵢ⁻¹)(F)`. The justification is the
following root computation, which is not formalized. Let `Σᵢ` be the reduced
roots of `Pᵢ`; then `−Σᵢ` are those of `P̄ᵢ`, and every reduced root lies in
exactly one of `Σᵢ` and `−Σᵢ`. Sorting a root of `Σ₂ ∩ −Σ₀` by whether it
lies in `Σ₁` gives the disjoint union
`Σ₂ ∩ −Σ₀ ⊆ (Σ₂ ∩ −Σ₁) ⊔ (Σ₁ ∩ −Σ₀)`. So
`d(P₂, P₀) ≤ d(P₂, P₁) + d(P₁, P₀)`, with equality exactly when the
inclusion is an equality. That happens exactly when no root lies in
`Σ₀ ∩ Σ₂` without lying in `Σ₁`. By negation it also happens exactly when no
root lies in `−Σ₀ ∩ −Σ₂` without lying in `−Σ₁`. The two conjuncts are the
group forms of these two root conditions. At the level of roots they are
equivalent. Both are assumed, so that the targets need no description of the
radicals by root subgroups.

**Measures.** Waldspurger normalizes all Haar measures by his special `K`.
The Library uses one arbitrary compact open subgroup `K` of `G(F)`: the Haar
measure on `U_G(ψ')(F)` and on `U_G(ψ)(F) ∩ U_G(ψ')(F)` each give mass one to
the part in `K`, and the quotient measure is the compatible one. These are
the published `radicalHaar`, `sourceIntersectionHaar` and
`DynamicSource.quotientMeasure`. For an arbitrary `K` the formula can fail by
a constant factor. If `K ∩ U₁` is not the product of `K ∩ U₀ ∩ U₁` and
`K ∩ U₁ ∩ Ū₀`, the measure on the complement `U₁ ∩ Ū₀` defined by
the quotient need not give `K ∩ U₁ ∩ Ū₀` mass one. The target therefore
assumes the two splittings `SplitsAlong K ψ₀ ψ₁` and `SplitsAlong K ψ₁ ψ₂`
of Worker 200's module `CommonLeviCompactSplitting`. `SplitsAlong K t m`
says that every point of `K ∩ U_G(m)` is a product `a b` with
`a ∈ K ∩ U_G(t⁻¹) ∩ U_G(m)` and `b ∈ K ∩ U_G(m) ∩ U_G(t)`. The target does not
assume that `K` is special or maximal.

**Squared modulus.** The Library's family of standard integrals between two
parabolics with Levi `M` (`standardInductionIntertwinerFamily`, module
`StandardInductionSelfComparison`) is defined only given the identity
`SquaredModulusCompatibility` (module `StandardIntertwiningTarget`) for the
two radicals. That identity is published for the opposite pair, conditional
on two structural premises (`conditionalSquaredModulus`, module
`DynamicOppositeStandardIntertwining`). This module does not derive it for an
arbitrary pair of dynamic radicals with a common Levi. The family `pairFamily` and the
main target take it as a hypothesis, one for each of the three pairs. Proofs
of a proposition are equal, so the choice of proof does not matter.

**Domains.** The source states the formula for rational families of
operators. The Library's family is defined on the full domain region, the
parameters where every source vector has absolutely convergent integrals.
The target is stated pointwise on the intersection of the three full domain
regions. It does not assert that this intersection is nonempty, and it does
not concern the rational continuation.

**Structural target as a hypothesis.** The main target takes the structural
target as its first hypothesis. This separates the geometry of the radicals
from the analysis of the integrals. A proof of the main target together with
a proof of the structural target gives IV.1 (12) for the actual families
without that hypothesis.

## The common Levi

Section `Decomposition` fixes a cocharacter `χ`.

- `commonDecomposition χ ψ hψ`: for `hψ : Z_G(ψ) = Z_G(χ)`, an equality of
  subgroup functors, the published semidirect decomposition of `P_G(ψ)(F)`
  rewritten as `P_G(ψ)(F) = M ⋉ U_G(ψ)(F)` with the literal Levi
  `M = levi χ`, not an isomorphic copy.
- `centralizer_inverseCocharacter_eq`: `Z_G(ψ⁻¹) = Z_G(χ)` under the same
  hypothesis.

## Borel structures

At namespace level the module puts local Borel instances on the radicals
`radical ψ`, the intersections `(radical ψ).subgroupOf (radical ψ')` and the
quotients `QuotientSpace (U := radical ψ) (radical ψ')`. They are at
namespace level because `SquaredModulusCompatibility` in the targets needs
them.

## Standard integrals between two parabolics with Levi `M`

Section `Families` fixes `χ`, a compact open subgroup `K` with compactness
proof `hK`, and cocharacters `ψ`, `ψ'` with the centralizer of `χ`.

- `pairIntersectionHaar K hK ψ ψ'`: the published `sourceIntersectionHaar`
  on `U_G(ψ)(F) ∩ U_G(ψ')(F)`, as a subgroup of `U_G(ψ')(F)`. It gives mass one
  to the part in `K`. `pairIntersectionHaar_rightInvariant` is its right
  invariance, from `sourceIntersectionHaar_rightInvariant_of_cover`.
- `pairQuotientMeasure K hK ψ ψ'`: the published
  `DynamicSource.quotientMeasure K hK ψ ψ'` on
  `(U_G(ψ)(F) ∩ U_G(ψ')(F)) \ U_G(ψ')(F)`.
  `pairQuotientMeasure_isCompatible` is its Weil compatibility with
  `radicalHaar ψ' K hK` and `pairIntersectionHaar K hK ψ ψ'`.
- `pairFullDomainRegion χ K hK ψ hψ ψ' A`: the published
  `standardIntertwiningFullDomainRegion` for the induction from `P_G(ψ)`,
  integration over `U_G(ψ')`, the parameter identification
  `parameterHomeomorph χ`, the norms `normCharacters χ` and
  `pairQuotientMeasure`. It is the set of unramified parameters `z` of the
  centralizer scheme of `χ` such that, for the twist of `A` by `z`, every
  source vector has absolutely convergent smooth-dual scalar integrals.
- `pairFamily χ K hK ψ hψ ψ' hψ' hδ A z`: for `z` in that region, the
  published `standardInductionIntertwinerFamily` with these measures. It is
  an intertwining map from the `P_G(ψ)`-normalized induction to the
  `P_G(ψ')`-normalized induction of the same unramified twist of `A`. This is
  `J_{P_G(ψ')|P_G(ψ)}` at `z`.
- `pairFamily_spec`: every value of `pairFamily` represents the original
  scalar integrals over `(U_G(ψ) ∩ U_G(ψ')) \ U_G(ψ')` at every source vector
  and every point of `G(F)` (`HasIntegral`).
- `forwardFullDomainRegion_eq_pair` and
  `pairFamily_inverse_eq_conditionalForwardFamily`: for `ψ = χ` and
  `ψ' = χ⁻¹`, with the published `conditionalSquaredModulus`, the region and
  the family are the published `forwardFullDomainRegion` and
  `conditionalForwardFamily` (`J_{P̄|P}`). Both hold by `rfl`.

## The distance condition

`IsDistanceAdditive ψ₀ ψ₁ ψ₂` is
`radical ψ₀ ⊓ radical ψ₂ ≤ radical ψ₁ ∧
oppositeRadical ψ₀ ⊓ oppositeRadical ψ₂ ≤ oppositeRadical ψ₁`. For the
choice of this form, see Provenance.

## The structural target

`DistanceAdditiveRadicalFactorizationStatement` quantifies over a
nonarchimedean local field `F`, an affine group scheme `G` of locally finite
type with `IsConnectedReductive G`, and cocharacters `ψ₀`, `ψ₁`, `ψ₂` with
`Z_G(ψ₁) = Z_G(ψ₀)`, `Z_G(ψ₂) = Z_G(ψ₀)` and `IsDistanceAdditive ψ₀ ψ₁ ψ₂`. It
asserts that there is an
`OrderedSubgroupFactorization U₀ U₁ U₂ V W` (module
`StandardIntertwiningFactorization`) for `Uᵢ = U_G(ψᵢ)(F)`,
`V = U₁ ∩ Ū₀` and `W = U₂ ∩ Ū₁`. That is: `V ≤ U₁`, `V ≤ U₂`, `W ≤ U₂`, and
the multiplication maps

- `(U₀ ∩ U₁) × V → U₁`, `(a, v) ↦ a v`,
- `(U₁ ∩ U₂) × W → U₂`, `(b, w) ↦ b w`,
- `(U₀ ∩ U₂) × (V × W) → U₂`, `(a, (v, w)) ↦ a v w`

are homeomorphisms.

Why it is expected to hold. The first two maps are instances of the
Library's `MatrixRepresentation.unipotentIntersectionProduct` (module
`HarmonicAnalysis.HarishChandraSchwartz.UnipotentIntersectionProduct`),
which gives `(U(χ) ∩ U(ξ)) × (U(χ⁻¹) ∩ U(ξ)) ≃ₜ U(ξ)`, `(h, k) ↦ h k`, when
`ξ(t) ∈ Z_G(χ)(F)` for some `t ∈ F×` with `tⁿ → 0` and
`Z_G(χ)(F) ∩ U(ξ)(F) = 1`. Take `(χ, ξ) = (ψ₀, ψ₁)` and `(χ, ξ) = (ψ₁, ψ₂)`.
By the root computation in Provenance, the inclusion `V ≤ U₂` is the group
form of `Σ₁ ∩ −Σ₀ ⊆ Σ₂`, which is equivalent to the distance condition. With `U₀ ∩ U₂ ≤ U₁`, the
first map restricts to `(U₀ ∩ U₂) × V ≃ U₁ ∩ U₂`. Composed with the second
map, this gives the third.

## The main target

`ConditionalDynamicCommonLeviCompositionStatement` quantifies over `F`, `G`
as above with `[Smooth G.X.hom]`, and takes:

- `_hfac`: the structural target;
- `_hG : IsConnectedReductive G`. The instance `[Smooth G.X.hom]` is needed
  by `SplitsAlong`. It is implied by `_hG`, whose field `smooth` is
  `Smooth G.X.hom`, so the instance binder does not restrict the target;
- a cocharacter `χ` with literal Levi `M = Z_G(χ)(F)`, and a compact open
  subgroup `K` with compactness proof `hK`;
- cocharacters `ψ₀`, `ψ₁`, `ψ₂` with centralizer equalities `h₀`, `h₁`, `h₂`
  to `Z_G(χ)`, and `_hd : IsDistanceAdditive ψ₀ ψ₁ ψ₂`;
- `_hK₁₀ : SplitsAlong K ψ₀ ψ₁` and `_hK₂₁ : SplitsAlong K ψ₁ ψ₂`;
- the squared-modulus identities `hδ₁₀`, `hδ₂₁`, `hδ₂₀` for the pairs
  `(ψ₀, ψ₁)`, `(ψ₁, ψ₂)` and `(ψ₀, ψ₂)`;
- a smooth representation `A` of `M`, an unramified parameter `z` with
  `hz₁₀`, `hz₂₁`, `hz₂₀` putting it in the three full domain regions, and a
  vector `f` of the `P₀`-normalized induction of the twist of `A` by `z`.

Its conclusion is

```
pairFamily χ K hK ψ₀ h₀ ψ₂ h₂ hδ₂₀ A ⟨z, hz₂₀⟩ f =
  pairFamily χ K hK ψ₁ h₁ ψ₂ h₂ hδ₂₁ A ⟨z, hz₂₁⟩
    (pairFamily χ K hK ψ₀ h₀ ψ₁ h₁ hδ₁₀ A ⟨z, hz₁₀⟩ f),
```

that is, `J_{P₂|P₀}(z) f = J_{P₂|P₁}(z) (J_{P₁|P₀}(z) f)` with
`Pᵢ = P_G(ψᵢ)`.

## Why the target is expected to hold

This argument is not formalized. Take a factorization `D` from `_hfac`. In
its charts the three quotients are `V`, `W` and `V × W`. For `x ∈ G(F)`,

- `(J_{P₁|P₀} f)(x) = ∫_V f(v x) dv`;
- `(J_{P₂|P₁} F)(g) = ∫_W F(w g) dw`;
- `(J_{P₂|P₀} f)(g) = ∫_{V × W} f(v w g) d(v, w)`,

for measures on `V` and `W` determined by the quotient measures. The
splittings fix these measures.

- `SplitsAlong K ψ₀ ψ₁` makes `K ∩ U₁` the product of `K ∩ U₀ ∩ U₁` and
  `K ∩ V`. Then the quotient measure on `(U₀ ∩ U₁) \ U₁` is the Haar measure
  of `V` with `mes(K ∩ V) = 1`.
- `SplitsAlong K ψ₁ ψ₂` gives, in the same way, the Haar measure of `W` with
  `mes(K ∩ W) = 1` on `(U₁ ∩ U₂) \ U₂`.
- If `x ∈ K ∩ U₁ ∩ U₂` is `a v` with `a ∈ K ∩ U₀ ∩ U₁` and `v ∈ K ∩ V`, then
  `v ∈ U₂`, so `a ∈ U₂`. So `K ∩ U₁ ∩ U₂` is the product of
  `K ∩ U₀ ∩ U₂` and `K ∩ V`. With the second splitting, the quotient measure
  on `(U₀ ∩ U₂) \ U₂` is the product of the two normalized Haar measures on
  `V × W`.

The two sides then agree by Fubini. The double integral converges
absolutely because `z` lies in the full domain region of `J_{P₂|P₀}` (`hz₂₀`)
and by Tonelli. Proved Library results are meant to carry out this
argument at the level of integrals:

- `Langlands.Plancherel.StandardIntertwining.DynamicSource.comp_hasIntegral` (module
  `StandardIntertwiningDynamicSource`) composes standard integrals on actual
  dynamic radicals, given an `OrderedSubgroupFactorization`, three local
  product identities of the compact open pieces and ordered absolute
  integrability;
- `Langlands.Plancherel.StandardIntertwining.OppositeCharts.comp_hasIntegral_of_hasCompactOpenProduct`
  (Worker 200, module `StandardIntertwiningOppositeCharts`) does this for
  source `P_G(χ⁻¹)`, middle `P_G(ψ)` and target `P_G(χ)`, deriving the outer
  local product identities from two `HasCompactOpenProduct` hypotheses.

The target is for an arbitrary triple, so it is not a special case of the
second result.

## Choice of `K`

The target does not show that a `K` with both splittings exists. In
`CommonLeviCompactSplitting`, `splitsAlong_of_factor` gives `SplitsAlong K t m`
for every `m` with the Levi of `t` when `K` has an Iwahori factorization
`K = (K ∩ U_G(t⁻¹))(K ∩ Z_G(t))(K ∩ U_G(t))`. So a `K` with Iwahori
factorizations along `ψ₀` and along `ψ₁` satisfies both hypotheses.
`exists_isCommonLeviSplitting` gives, for two cocharacters with the same
Levi points, compact open subgroups in every identity neighborhood with all
four splittings for that pair. A `K` for an arbitrary triple is not
constructed in the Library.

## Related Library modules

- `DynamicOppositeStandardIntertwining`: the dynamic data `parabolic`,
  `levi`, `radical`, `oppositeRadical`, `radicalHaar`, the parameter
  identification and the opposite families.
- `StandardInductionSelfComparison`: `standardIntertwiningFullDomainRegion`,
  `standardInductionIntertwinerFamily` and its specification.
- `StandardIntertwiningDynamicSource`, `StandardIntertwiningSourceFactors`:
  the source measures at one compact open subgroup.
- `StandardIntertwiningFactorization`: `OrderedSubgroupFactorization` and
  the generic composition theorem.
- `CommonLeviCompactSplitting` and `StandardIntertwiningOppositeCharts`
  (Worker 200): `SplitsAlong`, the opposite-source composition.
- `PQCompositionProductDecomposition` (Worker 102): the proved
  `PQCompositionProductStatement`, Renard VII.3.5 (i). It gives
  `V₁₃ = V₁₂ V₂₃` for `Vᵢⱼ = N̄ᵢ ∩ Nⱼ` under the distance condition, for
  represented parabolics in the framework of `RepresentedParabolic`. This is
  the analogue of the third chart for the complements. It is not connected to
  dynamic radicals here.
- `StandardInductionCanonicalScalarComposition` (Worker 200): equality of
  canonical scalars of two opposite pairs with a common Levi, conditional on
  eight composition identities of continued families on nonempty open sets
  of parameters. The present target concerns the families only pointwise on
  their full domain regions, not their continuation.

## Intended use

IV.1 (12) is the input of IV.3 (1) (independence of `j_P(π)` of
`P ∈ P(M)`) for `P' ∉ {P, P̄}`. The module `DynamicOppositePairScalar` covers
only `P' ∈ {P, P̄}`. This target is meant to give the composition
identities that the general case needs.

## Not proved here

The two targets. The squared-modulus identity for an arbitrary pair of
dynamic radicals with a common Levi. The root-theoretic description of
`IsDistanceAdditive`. Nonemptiness of the full domain regions. The rational
continuation of the composition identity. The existence of `K` with both
splittings for a triple.

## Axioms

The proved results use only `propext`, `Classical.choice` and `Quot.sound`.
The targets are `def … : Prop` and introduce no axioms.
