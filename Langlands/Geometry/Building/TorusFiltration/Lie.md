# The Lie filtration of the minimal congruent torus filtration

Let `F` be a nonarchimedean local field, `K = inertiaFixedField F` its maximal unramified
extension, `O = fixedFieldIntegers F` and `𝔪` its maximal ideal. For a `K`-torus `T`
(`hT : IsTorus T.toGrp`) the Library constructs smooth models
`𝒯_r = (minimalCongruentModel F T hT r).val` over `O`, with integral points the minimal
congruent filtration `T(K)_r = minimalCongruentPoints F T hT r` (`TorusFiltration.Construction`).

## Definition

`minimalCongruentLie F T hT r` is the Lie lattice of `𝒯_r`,

  `t(K)_r = Lie(𝒯_r) = (minimalCongruentModel F T hT r).val.lieLattice`,

an `O`-submodule of the Lie algebra `GenericLie O T.toGrp` of `T`. This is Kaletha–Prasad's
definition `t(k)_r = Lie(T_r)` (Proposition B.6.9 for the standard filtration of weakly induced
tori, and the filtration `t(k)^mc_r` of Propositions B.10.15–B.10.17 for the minimal congruent
filtration). Since a smooth model over the strictly Henselian ring `O` is determined by its
integral points (KP Corollary 2.10.11), the lattice does not depend on the choice of model:

- `lieLattice_le_of_integralPoints_le`: if `M` is smooth and `M(O) ⊆ N(O)`, then
  `Lie(M) ⊆ Lie(N)`. The identity of `T` extends to a model homomorphism `M → N`
  (KP Corollary 2.10.10, `IntegralModel.smoothHomExtension` through
  `exists_hom_of_map_integralPoints_le`), whose differential is the identity
  (`GenericLie.map_id`) and maps `Lie(M)` into `Lie(N)` (`Hom.map_lieLattice_le`).
- `lieLattice_eq_minimalCongruentLie`: every smooth model with integral points `T(K)_r` has
  Lie lattice `t(K)_r`.

## Properties proved here

- `minimalCongruentLie_antitone`: `r ≤ s → t(K)_s ⊆ t(K)_r`, from the previous comparison and
  the antitonicity of `T(K)_r` (`minimalCongruentPoints_antitone`).
- `minimalCongruentLie_isLattice`: `t(K)_r` is a lattice (`Submodule.IsLattice` over `K`), by
  `IntegralModel.lieLattice_isLattice` for the smooth model `𝒯_r`.
- `congruenceSubgroupAt_eq_minimalCongruentPoints`: for a smooth model `M` with integral points
  `T(K)_r` and a positive integer `k`, the level-`k` congruence subgroup
  `M.congruenceSubgroupAt k` is `T(K)_{r+k}`. For `k = 1` this is the congruence property of
  the filtration (`minimalCongruentCongruence`, KP Definition B.5.3 and Proposition B.10.10);
  the induction step applies it to the positive congruence model
  `M.positiveCongruenceModel π k`, which is smooth (`IntegralModel.dilatationStructure`), has
  integral points `M.congruenceSubgroupAt k`, and whose level-one congruence subgroup is
  `M.congruenceSubgroupAt (k + 1)` (`congruenceSubgroupAt_positiveCongruenceModel`).
- `map_minimalCongruentLie_le`: for a homomorphism of `K`-tori `f : T ⟶ U`, the differential
  `GenericLie.map O (CommGroupScheme.groupHom f)` maps `t(K)_r` into `u(K)_r`. The functoriality
  of the filtration (`minimalCongruentFunctoriality`, KP Proposition B.10.10) and KP
  Corollary 2.10.10 extend `f` to a model homomorphism `𝒯_r → 𝒰_r`.

## The Lie congruence, from KP Lemma A.5.13(4)

KP Lemma A.5.13(4) says that the Lie lattice of the level-`k` congruence model of a smooth
model `M` is `𝔪^k • Lie(M)`. The Library states it as
`IntegralModel.CongruenceModelLieLatticeStatement` (`IntegralModel.CongruenceLieStatements`);
this file does not prove it, and the two results below take it as the explicit argument `h𝔩`.

- `smul_lieLattice_eq_minimalCongruentLie h𝔩 r k hM hp`: for a smooth model `M` with integral
  points `T(K)_r`, `𝔪^k • Lie(M) = t(K)_{r+k}` for every natural `k`. By `h𝔩` the left side is
  the Lie lattice of the level-`k` congruence model `M.congruenceModel π k`; for `k > 0` that
  model is smooth with integral points `M.congruenceSubgroupAt k = T(K)_{r+k}`, so
  `lieLattice_eq_minimalCongruentLie` applies, and for `k = 0` it is `M` itself.
- `smul_minimalCongruentLie h𝔩 r k`: `𝔪^k • t(K)_r = t(K)_{r+k}`, the case `M = 𝒯_r`.
  For `k = 1` this is the Lie congruence `t(K)_{r+1} = 𝔪 • t(K)_r`.

## Implementation note

The lattice statement makes the tower instance `GenericLie.instIsScalarTower` a local instance
of high priority: the instance search through the intermediate-field structure of
`inertiaFixedField F` inside its separable closure does not terminate within the default limit.

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732` (PDF page = printed page
+ 31): Corollaries 2.10.10 and 2.10.11 (printed p. 124), Lemma A.5.13 (printed pp. 636–637),
Proposition B.6.9 (printed p. 673), Definition B.5.3 (printed p. 668), Proposition B.10.10 (printed p. 690), Propositions B.10.15
and B.10.16 (printed pp. 693–694).
