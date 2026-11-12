# Simple root subgroups and their opposites generate every root subgroup: proof

Authors: Worker 180.

The theorem `Langlands.GroupScheme.simpleRootSubgroupGeneration` has type
exactly `SimpleRootSubgroupGenerationStatement.{u}` (module
`Rational.SimpleRootSubgroupGenerationStatement`), at arbitrary universe `u`.
For a connected reductive `G` over any field, a maximal split torus
`i : S.toGrp ⟶ G`, a generic cocharacter `ν` and any subgroup functor `F`
of `G` containing the root subgroups of `α` and `-α` for every simple
relative root `α`, it proves `RelativeRoot.subgroup i a ≤ F` for every
relative root `a`. It uses only the standard axioms.

## Implemented proof

1. **Coxeter structure.** The published `relativeWeylCoxeter` gives a finite
   relative Weyl group `N(k)/Z(k)` with a Coxeter system `cs` labelled by the
   simple relative roots and realizing the root action
   (`IsRelativeWeylCoxeterRealization`). In particular (clause 2) the simple
   reflection of `α` sends every positive relative root other than `α` and
   `2 • α` to a positive relative root.

2. **Transport.** If a rational normalizing point `n` lies in `F(k)` and the
   root subgroup of `c` lies in `F`, then so does the root subgroup of
   `weylAction i n c`: for a point `g` of the latter,
   `RelativeRoot.normalizer_conj_mem` (for `n⁻¹`) puts `n⁻¹ g n` in the root
   subgroup of `c`, and conjugating back by the restriction of `n`, a point of
   `F`, gives `g`.

3. **Simple reflections in `F(k)`.** For a simple root `α`, the published
   `rootRankOneFactorization` applied to a nonidentity rational root point
   `x` (`RelativeRoot.exists_rootPoint_actual`) gives an opposite pair
   `(p₁, p₂)` in the root subgroup of `-α` with `p₁ x p₂` normalizing `i`.
   This point lies in `F(k)` by hypothesis, and its class is a relative
   reflection in `α` (`IsOppositeFactorPair.isRelativeReflection`), hence
   equals `cs.simple α` by
   `IsRelativeWeylCoxeterRealization.eq_simple_of_isRelativeReflection`.
   By `CoxeterSystem.simple_induction_left`, every element of the relative
   Weyl group has a representative in `F(k)`.

4. **Sign change.** By the same induction, for every Weyl element `w` and
   every positive root `c` with `w c` not positive, the root subgroups of `c`
   and `-c` lie in `F`. For `w = s_α w'`: if `w' c` is not positive, use the
   induction hypothesis; otherwise `w' c` is positive and `s_α (w' c)` is not,
   so `w' c` is `α` or `2 • α` by clause 2. The root subgroups of `±α` lie in
   `F` by hypothesis and those of `±2α` lie in those of `±α`
   (`RelativeRoot.subgroup_nsmul_le`); step 2 with a representative of
   `w'⁻¹` in `F(k)` transports them to `±c`.

5. **Conclusion.** For a relative root `β`, the reflection representative of
   step 3 for `β` sends `β` to `-β` (`IsOppositeFactorPair.weylAction_eq_neg`),
   and `-β` is a root (`weylAction_mapsTo_relativeRoots`). Genericity makes
   `β` or `-β` positive; step 4, applied to the positive one of them and to
   this reflection, puts the root subgroup of `β` in `F`.

No root-system classification, reducedness or splitness of `G` is used; the
nonreduced case is handled by the alternative `2 • α` in step 4.
