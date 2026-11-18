# The local line crux in semisimple rank one

Internal helper module of the Task 7586 proof of
`Langlands.GroupScheme.RankOneCentralCoverStatement`. It proves the proposition
`RankOneLocalCover.LocalLineCrux` (module `RankOneLocalCover`).

## The base point

`exists_coreData` works over an algebraically closed field. Its hypotheses:
- `G` connected reductive, `i` a split maximal torus whose roots are pairwise dependent;
- flag data `F`;
- a cocharacter `ν` whose centralizer and that of `-ν` are the torus;
- the two conjugation identities `U(ν) = U(-ν).comap (conj n⁻¹)` and
  `U(-ν) = U(ν).comap (conj n⁻¹)`.

It produces core data `D` (`RankOneFlagDimension.CoreData`) with `D.toFlagData = F` and
`D.ν = ν` or `D.ν = -ν`.

Proof:
1. The closed subgroup `U(-ν)` (`Dynamic.Affine.unipotentScheme`) is smooth (`dynamicSmooth`),
   connected, affine and unipotent (`dynamicUnipotentUnipotence`), hence solvable
   (`isSolvableGroupScheme_of_isUnipotent`).
2. `solvableProperFixedPoint` gives a rational point of the proper scheme `X = G/B` fixed by
   `U(-ν)`.
3. Torus limits preserve `U(-ν)`-fixedness (`SplitTorusLimitInduction.isFixed_evalZero_of_normalizes`)
   because the torus normalizes `U(-ν)`. The torus lies in the centralizer of `-ν` (`hZn`), which
   lies in `P(-ν)` (`Dynamic.centralizer_le_parabolic`), and `Dynamic.conj_mem_unipotent`
   applies. `limit_induction` therefore gives a point fixed by both `T` and `U(-ν)`.
4. By `FlagData.eq_or_eq_of_isFixed` this point is `x₀` or `x₁`.
   - If it is `x₀`, then `U(-ν) ⊆ B`, and core data exist for `ν`, with `hconj` from the first
     conjugation identity.
   - If it is `x₁ = n · x₀`, then `n⁻¹ U(-ν) n ⊆ B`, and the second conjugation identity gives
     `U(ν) ⊆ B`. Core data then exist for `-ν`, with `hconj` from the second identity.

`comp_innerIso_inv` records `u ≫ conj(n⁻¹) = n⁻¹ u n` on points.

## The kernel step

`CoreData.finrank_tangent_le_one` shows that the tangent of `U(ν)` has dimension at most one. It
applies the general Library curve construction
`HomogeneousQuotient.curveUnipotentDataOfPseudoReductive` to:
- the pseudo-reductive group `G` (`hG.isPseudoReductive`);
- the ordinary closed solvable Borel `b` (`D.borel.isClosedSubgroup`,
  `D.borel.isSolvableGroupScheme`), the quotient `q` and its exact fibres;
- the split torus (`hT`), its factor `t` and the cocharacter `ν`;
- the dimension bound `CoreData.topologicalKrullDim_le_one`;
- the noncontainment `CoreData.not_unipotent_le`, rewritten along `t ≫ b = i` (`D.ht`).

`CurveUnipotentData.finrank_tangent_le_one` then bounds the tangent dimension. The curve
construction treats the intersection `U(ν) ∩ B` itself, using the Library's
`Unipotent/CodimensionOneNormality`. The curve lemmas are general: they are used here with
`dim G/B ≤ 1` obtained by Białynicki-Birula limits, the fixed-point classification and the
Hartogs/purity argument of `RankOneFlagDimension`, not by the prescribed-Borel argument.

`finrank_weightSpace_eq_one`: a root `χ` positive on `ν` has a one-dimensional weight space when
the tangent of `U(ν)` has dimension at most one. The weight space lies in that tangent
(`RelativeRoot.weightSpace_le_tangentSubmodule_unipotent`) and is nonzero.

## The crux

`RankOneLocalCover.localLineCrux : LocalLineCrux`. Given a root `α`:
1. Take flag data with nonidentity Weyl point `n` (`RankOneFlag.nonempty_flagData`) and a
   cocharacter `ν₀` positive on `α` (`RankOneLocalAssembly.exists_latticePairing_pos`).
2. Put `ν = normalizerSymmetrizedCocharacter i n⁻¹ ν₀ = ν₀ - w ν₀`. Every root `β` pairs with
   `ν` as `2⟨β, ν₀⟩` (`latticePairing_normalizerSymmetrizedCocharacter`). In particular
   `⟨α, ν⟩ > 0`, and `-β` is a root for every root `β` (`weylAction_eq_neg_of_rankOne`).
3. The centralizers of `±ν` are the torus (`rankOne_centralizer_isRepresentedBy` with
   `dynamicCentralizerReductive`). The conjugation identities are
   `unipotent_normalizerSymmetrizedCocharacter_conj` for `ν₀` and `-ν₀`, using
   `normalizerSymmetrizedCocharacter i n⁻¹ (-ν₀) = -ν`.
4. `exists_coreData` and `CoreData.finrank_tangent_le_one` bound the tangent of `U(ν)` or of
   `U(-ν)`. `finrank_tangentSubmodule_unipotent_normalizerSymmetrized_eq_neg` (equal dimensions
   for `±ν`) bounds both.
5. Positive roots on `ν` are unique (`positive_roots_eq_of_tangentSubmodule_unipotent_finrank_le_one`),
   so `α` is the only root positive on `ν`. Since `-β` is a root, `-α` is the only root negative
   on `ν`.
6. The weight spaces of `α` and `-α` are lines by `finrank_weightSpace_eq_one`, for `ν` and `-ν`
   respectively.

## Provenance

Internal assembly of the Task 7586 helper modules and Library results named above. The kernel
step uses the general Library curve lemmas `curveUnipotentDataOfPseudoReductive` and
`unipotent_dimension_le_one`, applied to the ordinary flag variety. The operator ruled this use
admissible (message 782343fd, answering request 7865ee03). No consumer of these lemmas on the
excluded route, such as `positive_roots_eq_of_rankOne_curve_quotient`, is called. The
transitive dependencies were scanned and contain none of the excluded declarations.
