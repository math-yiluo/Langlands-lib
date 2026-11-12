# The rank-one Levi factor dichotomy: proof

Authors: Worker 180.

The theorem `Langlands.GroupScheme.rankOneLeviFactorDichotomy` has type
`RankOneLeviFactorDichotomyStatement.{u}` (module
`SimplyConnected.RankOneLeviDerivedGenerationReduction`), at arbitrary
universe `u`. For a simply connected `G` over any field with maximal split
torus `i : S.toGrp ⟶ G`, generic cocharacter `ν`, representative
`j : M ⟶ G` of the centralizer of `ν`, simple relative root `α`, rank-one
Levi factor `a : A ⟶ G` for `α`, derived subgroup `d : D ⟶ M` and closed
normal almost-simple `b : B ⟶ D`, it proves that the image of `B` in `G`
lies in the image of `A`, or that every point of `B` commutes with every
point of `A` in `G`. It uses only the standard axioms.

## Implemented proof

Write `IsRankOneLeviFactor i α a` as its seven components: `a` closed, `A`
simply connected, almost simple, of split rank one, containing the root
subgroup of `α`, centralizing every cocharacter `ζ` with
`latticePairing S α ζ = 0`, and normalized by every point centralizing all
such `ζ`.

1. **The Levi subgroup.** The published `standardCocharacter` gives a
   standard cocharacter `ζ` for `{α}` and identifies the published
   `standardLevi i ν {α}` with the dynamic centralizer of `ζ`. With finitely
   many simple roots (`relativeSimpleRootBasis`), the published
   `standardLevi_eq_cocharacterAnnihilatorCentralizer` identifies it with the
   common centralizer of all cocharacters orthogonal to `α`. So every point of
   `L = Z_G(ζ)` centralizes all these cocharacters, which is the hypothesis of
   condition 7. Let `l : L ⟶ G` be the affine representative
   `Dynamic.Affine.centralizerHom`; `L` is connected reductive by
   `dynamicCentralizerReductive`.

2. **Its derived group is simply connected.** `derivedSubgroupRepresentability`
   gives `dα : Gα ⟶ L` with `IsDerivedSubgroup dα`; `Gα` is semisimple by
   `derivedSubgroupSemisimple`. The published
   `dynamicCentralizer_eq_torusCentralizer_image`, applied to the chosen
   dominant split-torus image of the cocharacter
   (`IsSplitTorus.dominantFactorization`), presents `L` as the centralizer of
   a split subtorus, so `splitTorusCentralizerDerivedSimplyConnected` makes
   `Gα` simply connected.

3. **`A` is a normal subgroup of `Gα`.** Condition 6 for `ζ` puts `A` in `L`.
   `A` is perfect (`IsAlmostSimple.derivedSubgroup_eq_top`), so
   `mem_derivedSubgroup_comp` puts its points in the derived subgroup of `L`;
   factoring through the representatives gives `aG : A ⟶ Gα` with
   `aG ≫ dα ≫ l = a`, closed by `IsClosedSubgroup.of_comp`. Condition 7,
   applicable by step 1, shows that the image of `aG` is normal in `Gα`.

4. **The complement.** The published `semisimpleNormalIsogenyComplement`
   gives a semisimple closed normal subgroup `κ : K ⟶ Gα` whose points
   commute with those of `A`, such that multiplication `A ⊗ K ⟶ Gα` is a
   central isogeny; simple connectedness of `Gα` makes it an isomorphism.

5. **A reflection inside `A`.** By `IsRankOneLeviFactor.subgroup_neg_le_range`,
   `A` contains the root subgroups of `α` and `-α`; the rank-one
   factorization (`rootRankOneFactorization`) of a nonidentity rational point
   of the root subgroup of `α` therefore gives a rational point `n` of `A`
   normalizing `i` with `weylAction i n α = -α`. Let `σ` be its torus
   automorphism; then `σ.hom ≫ α = -α`, and the cocharacter
   `ν' + ν` with `ν' = ν ≫ σ.hom` is orthogonal to `α`.

6. **`K` centralizes `S`.** For a point `z` of `K` and a value `s = ν(t)` the
   identity
   `s * s = (s * n * s⁻¹ * n⁻¹) * (n * s * n⁻¹ * s)` holds. The first factor
   lies in `A` (condition 7 for `s`, which centralizes all cocharacters of
   the commutative torus), so it commutes with `z`; the second factor is
   `(ν' + ν)(t)` (by the normalizing property of `n` and
   `comp_innerIso_hom`), with which `z`, a point of `L`, commutes by step 1.
   So `z` commutes with every value of `2ν`. Since `2ν` is again generic,
   `IsSplitTorus.dynamicCentralizer_eq_torusCentralizer` identifies its
   centralizer with that of `ν`, i.e. with the range of `j`. Hence `K`
   factors through `M`.

7. **`K` lies in `D` and is normal there.** `K` is perfect
   (`semisimplePerfect`), so it factors through `d` by
   `mem_derivedSubgroup_comp`: this gives `κD : K ⟶ D`. The representative
   `j` is closed (it is isomorphic over `G` to the affine centralizer
   representative, `IsRepresentedBy.isoOfIsRepresentedBy_hom_comp`), `M` is
   connected reductive, `M` lies in `L`, and `D` maps to `Gα` by
   `δ : D ⟶ Gα` with `δ ≫ dα ≫ l = d ≫ j` (again `mem_derivedSubgroup_comp`).
   Then `κD ≫ δ = κ`, `κD` is closed, and its image is normal in `D` because
   the image of `κ` is normal in `Gα` and `δ` is a monomorphism. `D` is
   semisimple (`derivedSubgroupSemisimple`), so smooth and affine; `K` is
   smooth and connected.

8. **The dichotomy in `D`.** The published
   `IsAlmostSimple.range_le_or_commute_of_normal` applied to `b` and `κD` in
   `D` gives two cases.
   - If the image of `B` lies in that of `K`, then the points of `B` are
     points of `K`, which commute with the points of `A` (step 4): this is
     the second alternative.
   - If `B` commutes with `K` in `D`, let `pA` be the published
     `commutingFactorRetraction` onto `A` and `q` the second projection of the
     inverse of the multiplication isomorphism. Every point of `Gα` is the
     product of its `A`-part and its `K`-part. For a point of `B`, its image
     in `Gα` and its `A`-part commute with `K`, so its `K`-part is central in
     `K`. The homomorphism `f = b ≫ δ ≫ q : B ⟶ K` therefore has pairwise
     commuting values, so the range of its kernel inclusion contains all
     commutators; `K` is separated, the kernel inclusion is closed, and
     `B` is perfect, so `derivedSubgroup_le_range` shows that `f` is
     trivial. Hence every point of `B` maps to its `A`-part, i.e. into the
     image of `a`: this is the first alternative.

## Relation to the literature

The argument is the structural part of the first step of the proof of
Theorem A in Prasad–Raghunathan, *On the Kneser–Tits problem* (1985),
printed p.110, registered as `prasad-raghunathan-1985-kneser-tits`: the
derived group of the Levi of `α` is the product of the rank-one factor and
anisotropic factors contained in the minimal Levi. The proof here replaces
the Tits-index description by the complement of Milne, *Algebraic Groups*
(2022), Theorem 21.51 (in the Library, `semisimpleNormalIsogenyComplement`)
and the computation of step 6.
