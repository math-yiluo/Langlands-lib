# Split components of dynamic Levi subgroups

Author: Worker 228.

This module proves the split-component part of the target `LeviSplitComponentStatement`, which
is the second conjunct. It combines the factorization results of
[`SplitTorusFactorization`](SplitTorusFactorization.md), the torus factorizations of
[`LeviFactorization`](LeviFactorization.md), and the rank facts of
[`SplitRankTransport`](SplitRankTransport.md) and [`Torus/SplitMono`](../Torus/SplitMono.md).
All declarations are in `Langlands.GroupScheme`. Throughout, `k` is a field and `𝕊 = Spec k`.

## Auxiliary facts

* `IsClosedSubgroup.isAffineHom_source`: over any base `S`, if `j : M ⟶ G` is a closed subgroup
  and `G` has affine structure morphism, then so does `M`. The structure morphism of `M` is the
  closed immersion `j` followed by that of `G`, and closed immersions are affine.
* `card_le_of_isClosedSubgroup_of_iso`: let `eA : A ≅ 𝔾_m^I` and `eB : B ≅ 𝔾_m^J`, and let
  `f : A ⟶ B` be a closed subgroup. Then `Nat.card I ≤ Nat.card J`. The proof conjugates `f` by
  `eA` and `eB`, using the published `IsClosedSubgroup.iso_comp` and `comp_iso`, and applies
  `splitTorus.card_le_card_of_isClosedSubgroup`.

## Existence of a split component

`exists_isSplitComponent_of_factor`: let `M` be a group scheme over `𝕊`, `t : T ⟶ M` a closed
subgroup with `T` a split torus, and suppose every central split torus `a : A ⟶ M` factors as
`g ≫ t = a`. If `M` has some central split torus `a₀`, then `M` has a split component.

*Proof.* Let `P n` say that `M` has a central split torus `a : A ⟶ M` with an isomorphism
`A ≅ 𝔾_m^I` and `Nat.card I = n`. For such an `a`, the factor `g` with `g ≫ t = a` is a closed
subgroup (`IsClosedSubgroup.of_comp`), so `n ≤ Nat.card I_T` by
`card_le_of_isClosedSubgroup_of_iso`, where `T ≅ 𝔾_m^{I_T}`. Thus `P` is bounded and `P` holds at
the rank of `a₀`. Let `a : A ⟶ M` witness `P` at `N := Nat.findGreatest P (Nat.card I_T)`. Take
a central split torus `a' : A' ⟶ M`, with `A' ≅ 𝔾_m^{I'}`, and `f : A ⟶ A'` with `f ≫ a' = a`.
Then `f` is a closed subgroup, hence a monomorphism. Maximality of `N` gives
`Nat.card I' ≤ N = Nat.card I`. So `f` is an isomorphism by `splitTorus.isIso_of_mono_of_iso`,
and `a` is a split component.

## The main theorem

`leviSplitComponent_factorization`: let `G` have affine structure morphism, let `i : T ⟶ G` be
a maximal split torus, `ν` a cocharacter of `T`, and `j : M ⟶ G` a closed subgroup representing
the dynamic centralizer `Dynamic.centralizer (groupHom ν ≫ i)`. Let `iG : A_G ⟶ G` be a split
component of `G`. Then there are a split component `iM : A_M ⟶ M` and homomorphisms
`f : A_G ⟶ A_M` and `g : A_M ⟶ T` such that

* `f ≫ iM ≫ j = iG`,
* `g ≫ i = iM ≫ j`,
* `(characterRestrict f).comp ((characterRestrict iM).comp (characterRestrict j)) =
  characterRestrict iG`.

This is exactly the second conjunct of `LeviSplitComponentStatement` for these data. Its
hypothesis `[IsAffineHom G.X.hom]` is a field of `IsConnectedReductive G`.

*Proof.*

1. `M` has affine structure morphism (`IsClosedSubgroup.isAffineHom_source`).
2. `t := Dynamic.torusFactor` is a homomorphism `T ⟶ M` with `t ≫ j = i`
   (`Dynamic.torusFactor_comp`). So `t ≫ j` is a maximal split torus of `G`, and `t` is a closed
   subgroup (`IsClosedSubgroup.of_comp`).
3. Every central split torus of `M` factors through `t`
   (`IsCentralSplitTorus.exists_factor_of_isMaximalSplitTorus`).
4. `aG := Dynamic.centralizerFactor` is a homomorphism `A_G ⟶ M` with `aG ≫ j = iG`, and
   `aG` is a central split torus of `M`
   (`IsCentralSplitTorus.isCentralSplitTorus_centralizerFactor`).
5. Step 3 and `aG` let `exists_isSplitComponent_of_factor` produce a split component
   `iM : A_M ⟶ M`.
6. `IsSplitComponent.exists_factor` factors the central homomorphism `aG` from the split torus
   `A_G` through `iM`, as `f ≫ iM = aG`. Hence `f ≫ iM ≫ j = iG`.
7. Step 3 applied to `iM` gives `g` with `g ≫ t = iM`, so `g ≫ i = g ≫ t ≫ j = iM ≫ j`.
8. The character identity is `characterRestrict_chain` applied to `f ≫ iM ≫ j = iG`.

## Provenance

The statement is the split-component part of Renard, *Représentations des groupes réductifs
p-adiques*, V.3.6, for the actual dynamic Levi subgroup. The route is specific to this
formalization: images of products of split tori and a maximal-rank choice of central split
torus. It uses the published definitions `IsSplitComponent`, `IsCentralSplitTorus` and
`IsMaximalSplitTorus`, and makes no further claim from the literature.
