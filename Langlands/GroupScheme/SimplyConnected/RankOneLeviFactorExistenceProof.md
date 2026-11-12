# Existence of rank-one Levi factors

Authors: Worker 4896.

`Langlands.GroupScheme.rankOneLeviFactorExistence` proves exactly the published
proposition `Langlands.GroupScheme.RankOneLeviFactorExistenceStatement.{u}`
(module `Langlands.GroupScheme.SimplyConnected.RankOneLeviFactors`), in
arbitrary universe `u`. Its type is that proposition, with no added hypothesis
or proposition-valued parameter. The field is arbitrary: finite and imperfect
fields and every characteristic are included. The development check reports
only the axioms `propext`, `Classical.choice` and `Quot.sound`.

The statement: for a field `k`, an affine simply connected group scheme `G`
over `Spec k`, a maximal split torus `i : S.toGrp ⟶ G`, a generic cocharacter
`ν`, a representative `j : M ⟶ G` of
`Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)` and a simple relative root
`α ∈ simpleRelativeRoots i ν`, there are `A` and `a : A ⟶ G` with
`IsRankOneLeviFactor i α a`, `IsConnectedReductive (subgroupIntersection j a)`,
and `IsSimplyConnected D` for every derived subgroup `d : D ⟶ subgroupIntersection j a`.

The proof uses the two supporting modules
`Langlands.GroupScheme.Rational.RootOrthogonalCentralizer` and
`Langlands.GroupScheme.ProductFactorInclusion`, submitted with this one, and
published Library theorems named below. Write `⟨χ, ζ⟩` for
`latticePairing S χ ζ`.

## Construction of the factor

1. **The Levi subgroup.** `G` is connected reductive, smooth, affine and
   connected, and `S` is split. Since `α` is a positive relative root and `ν`
   is generic, `⟨α, ν⟩ ≠ 0`. `IsSplitTorus.exists_rootOrthogonalCocharacter`
   gives `ζ₀` with `⟨α, ζ₀⟩ = 0` such that
   `⟨α, ν⟩ • β = ⟨β, ν⟩ • α` for every relative root `β` with
   `⟨β, ζ₀⟩ = 0`. Let `χ₀ = CommGroupScheme.groupHom ζ₀ ≫ i`, and let
   `l : L ⟶ G` be the published closed affine centralizer representative
   `Dynamic.Affine.centralizerHom χ₀`. The published
   `dynamicCentralizerReductive` makes `L` connected reductive. The image of
   `i` centralizes `χ₀` (`range_le_torusCentralizer`,
   `torusCentralizer_le_dynamicCentralizer`), so
   `IsMaximalSplitTorus.lift` gives a maximal split torus `iL : S.toGrp ⟶ L`
   with `iL ≫ l = i`.
2. **The derived subgroup.** The published `reductiveCentralDerivedProduct`
   gives a central torus `z : Z.toGrp ⟶ L` and a derived subgroup `d : D ⟶ L`
   whose product map `subgroupProductMap z d` is an epimorphism. `D` is
   semisimple (`derivedSubgroupSemisimple`). It is simply connected by
   `splitTorusCentralizerDerivedSimplyConnected`, applied to the closed split
   torus image of `χ₀` (`IsSplitTorus.dominantFactorization`), whose
   centralizer is `Dynamic.centralizer χ₀`
   (`dynamicCentralizer_eq_torusCentralizer_image`) and so is represented by
   `l`.
3. **Tori.** The published `derivedMaximalSplitTorus` gives a maximal split
   torus `jD : SD.toGrp ⟶ D` and `e : SD ⟶ S` with
   `jD ≫ d = groupHom e ≫ iL`. The published `splitComponentStatement` gives a
   split component `aC : C.toGrp ⟶ L`. It factors as `groupHom c ≫ iL`
   through the maximal split torus
   (`IsCentralSplitTorus.exists_factor_of_isMaximalSplitTorus`), so
   `groupHom c ≫ iL` is central. The published
   `derivedCentralSplitTorusProduct` makes
   `RelativeRoot.centralComplementProduct e c : SD.toGrp ⊗ C.toGrp ⟶ S.toGrp`
   a central isogeny; in particular it is finite, flat and surjective.
4. **The root on `SD`.** `α` is a root of `L`, by
   `mem_relativeRoots_of_pairing_eq_zero` since `⟨α, ζ₀⟩ = 0`. The published
   `RelativeRoot.mem_relativeRoots_precomp_derived` then makes `e ≫ α` a
   relative root of `jD`; in particular `e ≫ α ≠ 0`.
5. **`D` has split rank at most one.** Every root of `jD` is `e ≫ β` for a
   root `β` of `iL` (`RelativeRoot.exists_relativeRoot_precomp_eq_derived`).
   Such `β` is a root of `i` with `⟨β, ζ₀⟩ = 0` (`relativeRoots_subset_of_factor`,
   `relativeRoot_pairing_eq_zero_of_le_dynamicCentralizer`), so
   `⟨α, ν⟩ • (e ≫ β) = ⟨β, ν⟩ • (e ≫ α)`.
   `IsSemisimple.splitTorusRank_le_one_of_smul_roots` (below) gives
   `splitTorusRank SD ≤ 1`. The published `relativeRankIdentity` identifies
   `splitRank D` with `splitTorusRank SD`.
6. **The factor.** The published `IsSimplyConnected.almostSimpleProduct`
   gives an isomorphism `D ≅ pi P.factor` onto a finite product of simply
   connected almost-simple groups. `exists_piSingle_factorization` (below)
   gives an index `x₀` and `s : SD.toGrp ⟶ A`, where `A = P.factor x₀`, with
   `jD ≫ P.iso.hom = s ≫ piSingle P.factor x₀`. Put
   `h = (piSingle P.factor x₀ ≫ P.iso.inv) ≫ d : A ⟶ L` and `a = h ≫ l`.

## Verification of `IsRankOneLeviFactor i α a`

- *Closed subgroup.* `piSingle` is closed (`isClosedSubgroup_piSingle`), and so
  are `P.iso.inv`, `d` and `l`.
- *Simply connected and almost simple.* These are the fields of the product
  decomposition at `x₀`.
- *Split rank one.* `splitRank A ≤ splitRank D ≤ 1` by
  `splitRank_le_of_isClosedSubgroup`. The map `s` is a closed subgroup
  (`IsClosedSubgroup.of_comp`, since `s ≫ piSingle` equals the closed
  `jD ≫ P.iso.hom`). If `SD ≅ splitTorus I` had `I` empty, every point of `SD`
  would be trivial and the character `e ≫ α` would vanish. So
  `1 ≤ Nat.card I ≤ splitRank A` by `card_le_splitRank`.
- *Normality in `L`.* The image of `piSingle` is normal in the product
  (`isNormal_range_piSingle`). Its transport by `P.iso.inv` is normal in `D`
  (`SubgroupFunctor.IsNormal.range_comp_iso`). The published
  `SubgroupFunctor.IsNormal.range_comp_of_isCentral_of_epi_subgroupProductMap`
  then makes the image of `h` normal in `L`, using the central torus and the
  epimorphic product of step 2.
- *Root subgroup.* From `jD = s ≫ piSingle ≫ P.iso.inv` and step 3,
  `groupHom e ≫ iL = s ≫ h`. The published
  `RelativeRoot.subgroup_le_range_of_restriction_ne_zero`, with `e ≫ α ≠ 0`,
  gives `RelativeRoot.subgroup iL α ≤ range h`. The root subgroup of `i` lies
  in `range l`: it is fixed by the cocharacter `ζ₀` because `ζ₀ ≫ α = 0`
  (`RelativeRoot.subgroup_le_fixedSubgroup_of_restriction_eq_zero`,
  `AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer`,
  `torusCentralizer_gm_eq_dynamicCentralizer`). Its preimage under `l` is
  `RelativeRoot.subgroup iL α` (`RelativeRoot.subgroup_comap_closedEmbedding`,
  with the flatness instances of `RelativeRoot.characterFpqc`). Hence
  `RelativeRoot.subgroup i α ≤ range a`.
- *Centralizing orthogonal cocharacters.* `range a ≤ range l`, which is the
  centralizer of `χ₀`, and `dynamicCentralizer_le_of_rootOrthogonal` gives
  containment in the centralizer of every `ζ` with `⟨α, ζ⟩ = 0`.
- *Normalized by the common centralizer.* A point `g` centralizing all these
  cocharacters centralizes `ζ₀`, so `g = g' ≫ l`. For `x = w ≫ a`, normality
  of the image of `h` in `L` writes `g' * (w ≫ h) * g'⁻¹` as `w' ≫ h`, so
  `g * x * g⁻¹ = w' ≫ a`.

## The intersection with `M`

Let `N = subgroupIntersection j a` with second projection `sn : N ⟶ A`. The
projection is a monomorphism because `j` is one and the intersection is a
pullback (`IsPullback.mono_snd_of_mono`). Since `ν` is generic,
`range j = torusCentralizer i` (`IsSplitTorus.dynamicCentralizer_eq_torusCentralizer`).
For every point `t` of `SD`, the identity `groupHom e ≫ iL = s ≫ h` gives
`(t ≫ e) ≫ i = (t ≫ s) ≫ a`. The proof shows
`range sn = torusCentralizer s`:

- If `x = y ≫ sn`, then `x ≫ a` lies in `range j`, hence commutes with the
  points of `i`, in particular with every `(t ≫ s) ≫ a`. Since `a` is a
  monomorphism, `x` commutes with every `t ≫ s` (`Commute.of_comp_hom`).
- Conversely let `x` centralize `s`. Make the product
  `SD.toGrp ⊗ C.toGrp` a commutative group scheme `PC`. The isogeny
  `p = centralComplementProduct e c` is finite and surjective, and `S` is
  reduced because it is smooth over `k`. So `p` is schematically dominant
  (`IsSchemeTheoreticallyDominant.of_isDominant`), and the published
  `torusCentralizer_comp_eq_of_isSchemeTheoreticallyDominant` gives
  `torusCentralizer (p ≫ i) = torusCentralizer i`. A point of `PC` is a pair
  `(t₁, t₂)`, and `p` maps it to the product of the images of `t₁` and `t₂`
  (`comp_prodHom`). Now `x ≫ a` commutes with `(t₁ ≫ e) ≫ i = (t₁ ≫ s) ≫ a`
  because `x` centralizes `s`. It commutes with `(t₂ ≫ c) ≫ i` because that
  point is the image under `l` of a central point of `L` (step 3), while
  `x ≫ a` is the image under `l` of a point of `L`. Hence `x ≫ a ∈ range j`,
  and the pullback property gives a point of `N` mapping to `x`.

So `sn` represents `torusCentralizer s`, where `s` is a closed split subtorus
of the simply connected group `A`. The published
`splitTorusCentralizerReductive` makes `N` connected reductive, and the published
`splitTorusCentralizerDerivedSimplyConnected` makes every derived subgroup of
`N` simply connected.

## Auxiliary results in this module

- `Commute.comp_hom` and `Commute.of_comp_hom`: homomorphisms preserve
  commuting points, and monomorphic ones reflect them.
- `SubgroupFunctor.IsNormal.range_comp_iso`: normality of an image is
  preserved by an isomorphism of the ambient group.
- `character_eq_zero_of_points_eq_one`: if every point of a commutative group
  scheme is `1`, every character is `0` (`CommGroupScheme.hom_ext_points`).
- `isAffineHom_of_iso`: a group scheme isomorphic to an affine one is affine.
- `IsSemisimple.splitTorusRank_le_one_of_smul_roots`: let `D` be semisimple
  and affine, `j : T.toGrp ⟶ D` a closed split torus, `α'` a character and
  `n ≠ 0` such that every root `γ` of `j` satisfies `n • γ = m • α'` for some
  integer `m`. Then `splitTorusRank T ≤ 1`. Otherwise the line
  `ℚ · (1 ⊗ α')` is a proper subspace of `ℚ ⊗ characterLattice T`, so a
  nonzero linear form `f` vanishes on it
  (`Submodule.exists_dual_map_eq_bot_of_lt_top`).
  `IsSplitTorus.exists_positive_multiple_pairing` realizes a positive multiple
  of `f` as a cocharacter `ζ`. Then `⟨α', ζ⟩ = 0`, hence `⟨γ, ζ⟩ = 0` for every
  root `γ`, so `ζ = 0` by the published
  `IsSemisimple.cocharacter_eq_zero_of_annihilates_relativeRoots`. Then `f`
  vanishes on every `1 ⊗ χ`, so `f = 0`, a contradiction.
- `IsSplitTorus.exists_closed_splitTorus_of_ne_zero`: a nonzero homomorphism
  `σ` from a split torus into an affine group factors through a closed split
  subtorus (`IsSplitTorus.exists_factor_isSplitSubtorus`). Writing that
  subtorus as `splitTorus J`, the set `J` is nonempty, since otherwise all
  homomorphisms out of it vanish (`splitTorus.subsingleton_hom_of_isEmpty`)
  and so would `σ`.
- `exists_piSingle_factorization`: let `D` be affine with
  `splitRank D ≤ 1`, let `φ : D ≅ pi F` with all `F x` affine, and let
  `j : T.toGrp ⟶ D` be a closed split torus carrying a nonzero character.
  Then `j ≫ φ.hom = s ≫ piSingle F x` for some `x` and `s`. Let
  `σ y = j ≫ φ.hom ≫ Pi.π F y`. If all `σ y` vanished, `j` would be `0`.
  Being a monomorphism, it would make every point of `T` trivial, so every
  character would vanish. Pick `x` with `σ x ≠ 0`. If also `σ y ≠ 0` for some
  `y ≠ x`, the previous lemma and `card_add_card_le_splitRank_pi` would give
  `2 ≤ splitRank (pi F) = splitRank D ≤ 1`. So `σ y = 0` for `y ≠ x`, and
  `eq_comp_piSingle` gives the factorization.

## Sources and provenance

The construction follows G. Prasad and M. S. Raghunathan, *On the Kneser–Tits
problem*, Comment. Math. Helv. 60 (1985), registered as
`prasad-raghunathan-1985-kneser-tits`, §1.5–1.6, printed pp.108–109. There
`G_Θ` is the isotropic `k`-simple factor of the derived group of the Levi
subgroup `M_Θ` attached to the simple relative root, and `ℳ_Θ = M ∩ G_Θ` is the
centralizer of its maximal split torus. The Lean proof realizes `M_Θ` as the
centralizer of the single cocharacter `ζ₀` and selects the factor as the one
containing the maximal split torus of the derived group. The split-rank bound
replaces the Tits-index argument by the root computation of step 5. The
implementation is otherwise an internal composition of the published Library
results named above.
