# Special tori from an adapted smooth model (KP Proposition 9.3.4)

Worker 224. This module reduces `Langlands.Geometry.Building.SpecialTorusExistenceStatement`
(Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, Proposition 9.3.4) to the building input
`SpecialTorusIntegralModelStatement` (an adapted smooth model; see its Markdown). The Henselian
lifting of a torus of the special fibre (KP Proposition 8.2.1(1)) is the published Library
theorem `HenselianTorusLifting.nonempty_liftData` (module
`Langlands.GroupScheme.Torus.HenselianSubgroupLifting`). The unconditional theorem
`specialTorusExistence`, in module `Langlands.Geometry.Building.SpecialTorusExistenceProof`,
applies this reduction to the published proof `specialTorusIntegralModel`.

The argument follows the proof of KP 9.3.4 (printed p. 332): lift a maximal torus of the special
fibre that contains the closed fibre of the split torus. The lift splits over the integers of the
maximal unramified extension, and its generic fibre, together with `S`, generates the required
torus. The implemented route differs from KP in two places, described below: the torus is formed
as a schematic image over `F`, and its maximality over `K` comes from a rank count. All steps use
published Library results or the helper modules of this proof, which are listed below.

## Notation

`F` is a nonarchimedean local field with integers `O = 𝒪[F]` and residue field `k = 𝓀[F]`. `K`
is the maximal unramified extension `inertiaFixedField F`, with integers
`O_K = fixedFieldIntegers F` and residue field `k'`, which is an algebraic closure of `k`.

## Declarations

`IntegralModel.commute_generic_of_torusCentralizer`: let `M` be an integral model over a domain
`R` of a group `G` over its fraction field `K`, `𝒮` a commutative group over `R` with
`j : 𝒮 ⟶ M`, and `eS : 𝒮_K ≅ S` with `genericTorusMap 𝒮 j = eS ≫ iS`. Let `z : Z ⟶ M` represent
the centralizer of `j` and let `i : 𝒯 ⟶ Z` be any homomorphism. Then for all points `x` of `S`
and `y` of `𝒯_K` over the same test scheme, `iS(x)` and `t₁(y)` commute, where
`t₁ := (i ≫ z)_K ≫ genericIso`. Proof: the centralizer is compatible with base change
(`torusCentralizer_baseChange`, `IsRepresentedBy.baseChange`). So `(i ≫ z)_K(y)` lies in the
centralizer of `j_K`, and it commutes with `j_K(eS⁻¹(x))`. Composing with the group homomorphism
`genericIso` (`MonObj.mul_comp`) and using `iS = eS⁻¹ ≫ j_K ≫ genericIso` gives the claim.

`specialTorus_genericSquare`: `Spec K ⟶ Spec F ⟶ Spec O` equals
`Spec K ⟶ Spec O_K ⟶ Spec O`. Both composites are `Spec` of the same ring map `O → K`.

`exists_specialTorus_of_model`: let `G` be connected
reductive over `F` with a maximal split torus `iS : S ⟶ G`. Let `M` be a smooth `O`-model of `G`
with connected special fibre, `𝒮` a closed split `O`-torus `j : 𝒮 ⟶ M` with generic fibre `S`
(through `eS`), and `𝒜` a closed split `O_K`-torus `a : 𝒜 ⟶ M_{O_K}` whose generic fibre is a
maximal `K`-split torus of `G_K`. Then there are a commutative group `T` over `F`, a closed
subgroup `iT : T ⟶ G` and `f : S ⟶ T` with `f ≫ iT = iS`, such that `T_K ⟶ G_K` is a maximal
`K`-split torus. These are the conclusions of `SpecialTorusExistenceStatement` for this `G`
and `S`.

`specialTorusExistence_of_integralModel`: `SpecialTorusIntegralModelStatement` implies
`SpecialTorusExistenceStatement`. The building statement provides the model, `𝒮` and `𝒜`, and
`exists_specialTorus_of_model` concludes.

## Proof of `exists_specialTorus_of_model`

1. *Centralizer.* `M` is smooth and affine and `𝒮` is split, so the centralizer of `j` is
   represented by a smooth closed subgroup `z : Z ⟶ M`
   (`splitTorusCentralizer_hasSmoothClosedRepresentative_overRing`).
2. *Maximal torus of the special fibre.* `𝒮_k` is a torus, and `j_k` is closed. So
   `EnvelopeInfiniteReduction.exists_isMaximalTorus_factor` gives a maximal torus
   `t₀' : T₀ ⟶ M_k` through which `j_k` factors. Then `T₀` centralizes `𝒮_k`
   (`range_le_torusCentralizer_of_factor`), so `t₀'` factors as `t₀ ≫ z_k` with `t₀` closed
   (`IsRepresentedBy.factorHom`, `IsClosedSubgroup.of_comp`).
3. *Lift.* `O` is Henselian (`henselianLocalRing_integer`), `O → k` is surjective, and `Z` is
   smooth and affine. `T₀` is a torus over `k`, so it is a relative torus
   (`IsTorus.isRelativeTorus`, Library module `RelativeFieldComparison`).
   `HenselianTorusLifting.nonempty_liftData` (Library module `HenselianSubgroupLifting`) then
   gives lifting data for `t₀`: a relative torus `𝒯` over `O`, a closed subgroup
   `i : 𝒯 ⟶ Z` and an isomorphism `e : 𝒯_k ≅ T₀`. The proof uses `𝒯`, `i`, closedness, the
   relative-torus property and `e`. It does not use the compatibility `i_k = e ≫ t₀`.
4. *Splitting over `O_K`.* `O_K` is Henselian with separably closed residue field, so the
   relative torus `𝒯_{O_K}` is split, `𝒯_{O_K} ≅ splitTorus I`
   (`RelativeTorus.IsTorus.isSplitTorus_of_isSepClosed`, helper module
   `StrictHenselianRelativeSplit`).
5. *Rank bound from the special fibre.* `k' ⊇ k` is algebraically closed, and the residue
   square `Spec k' ⟶ Spec k ⟶ Spec O = Spec k' ⟶ Spec O_K ⟶ Spec O` holds
   (`IntegralModel.unramifiedResidue_specMap_comp`). `card_le_card_of_residue_isMaximalTorus`
   (helper module `ResidueRankComparison`) compares the closed split torus `𝒜 ≅ splitTorus JA`
   with the maximal torus `T₀` over `k'`: `#JA ≤ #I`.
6. *Generic fibre.* Put `T₁ := 𝒯_F` and `t₁ := (i ≫ z)_F ≫ genericIso`, a closed subgroup of
   `G`. Its base change to `K` is `(𝒯_{O_K})_K ≅ splitTorus I` (`baseChangeSquareIso` along
   `specialTorus_genericSquare`, then `splitTorus.baseChangeIso`).
7. *Commuting.* `S` and `T₁` commute in `G` by `commute_generic_of_torusCentralizer`.
8. *The torus.* `S_K` and `(T₁)_K` are split. `exists_closedTorus_of_commute` (helper module
   `CommutingTorusImage`) gives a closed commutative `iT : T ⟶ G` with `f : S ⟶ T`,
   `g : T₁ ⟶ T`, `f ≫ iT = iS`, `g ≫ iT = t₁` and `T_K ≅ splitTorus J`. Since `g_K ≫ iT_K`
   is closed, `card_le_card_of_comp_isClosedSubgroup` gives `#I ≤ #J`.
9. *Maximality.* `G_K` is connected reductive (`connectedReductiveFieldExtensionStatement`),
   so all its maximal split tori have the same rank (`maximalSplitTorusConjugacy`, part 2).
   `T_K ⟶ G_K` is a closed split subtorus with `#JA ≤ #J`, where `𝒜_K` is maximal split.
   `IsSplitSubtorus.isMaximalSplitTorus_of_card_le` (helper module `SplitRankMaximality`)
   concludes that `T_K` is a maximal split torus.

KP builds the torus over `O` and proves maximality through the apartment. Here, step 8 forms the
torus over `F` as a schematic image. Step 9 replaces the apartment argument by the rank count
of steps 5 and 8. Because of this, `𝒮 ⊆ 𝒯` over `O` is never needed.

`exists_specialTorus_of_model` sets `maxHeartbeats` to 800000 because of the cumulative length
of its proof.
