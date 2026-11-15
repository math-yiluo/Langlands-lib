# Reduction of the multipliable zero-value lift to a field comparison

This module proves `unramifiedZeroJumpLiftMultipliable_of_fieldComparison`:

```
UnramifiedZeroJumpFieldComparisonStatement.{u} → UnramifiedZeroJumpLiftMultipliableStatement.{u}
```

`UnramifiedZeroJumpLiftMultipliableStatement` (module
`UnramifiedAffineRootRestrictionReduction`) is one of the three inputs of
`unramifiedAffineRootRestriction_of_zeroJumps`, which derives
`UnramifiedAffineRootRestrictionStatement` (Kaletha–Prasad Proposition 9.4.28).
`UnramifiedZeroJumpFieldComparisonStatement` (module of the same name) is unproved.

The main ingredient is a lemma over any field extension `K/k` and any real level `r`,
`exists_rootJump_lift_of_torusRestrictedJump`. A filtration jump for the torus restriction
of a root-datum valuation lifts to a filtration jump of some root of the larger torus. The
module also contains the helper lemmas used in its proof. Nothing in the module assumes an
unproved statement except the hypothesis of the reduction theorem.

## Notation

In section `Lift`, `k ⊆ K` are fields, `G` is a smooth affine group scheme over `k`, and
`i : S.toGrp ⟶ G` is a closed embedding of a torus (`[Mono i.hom.hom.left]`). As local
notation, `b = algebraBaseMap k K`, `S_K`, `G_K`, `i_K` are the base changes, and
`a_K = characterLattice.baseChange b S a`. `T` is a torus over `K` with
`j : T.toGrp ⟶ G_K`, and `f : S_K ⟶ T` satisfies `hfactor : groupHom f ≫ j = i_K`.
`φ : RootFunctionFamily T G_K` is a root-datum valuation for `j` (`hφ`), and `hE` and
`hEbase` are the opposite-factor-pair hypotheses for `j` and for `i`. The torus
restriction of `φ` along `f` is `torusRestrictedRootFunctionFamily (i := j) (hS.baseChange b)
hT hE hφ f`, a family of root functions for `groupHom f ≫ j : S_K → G_K`.

A private instance `multipliableLiftAffine` records that `G_K → Spec K` is affine. It is
the same instance as in `RootValueTorusFieldRestriction`, where it is also private.

## Helper lemmas

- `list_ofFn_prod_mul_of_commute`: in a group, if every `v l` lies in a subgroup `P` and
  every `z l` commutes with every element of `P`, then
  `∏ (v l * z l) = (∏ v l) * (∏ z l)` (ordered products over `Fin n`).
- `filtrationSubgroup_le_torusRestrictedRootDepthSubgroup`: if `χ` is a root of `j` with
  `f ≫ χ = m • β` and `m > 0`, then `hφ.filtrationSubgroup χ (m * s)` lies in
  `torusRestrictedRootDepthSubgroup hφ f β s`. This is one term of the supremum that
  defines the right side.
- `nsmul_mem_and_le_two_of_restrict_eq`: if `α ∈ Φ(S)`, `χ ∈ Φ(T)` and `f ≫ χ = m • α_K`
  with `m > 0`, then `m • α ∈ Φ(S)` and `m ≤ 2`. The restriction is a root of `i_K`
  (`rootRestriction`), hence `m • α` is a root of `i` (`mem_roots_baseChange_iff`), and
  `HasOppositeFactorPairs.nat_multiple_le_two` bounds `m`.
- `rootGroupPoints_le_doubleRootGroupPoints_of_restrict_eq_two_nsmul`: if `f ≫ χ = 2 • α_K`
  with `α ≠ 0`, then `U_χ(K) ⊆ U_{2α_K}(K)`, where the right side is
  `doubleRootGroupPoints (groupHom f ≫ j) α_K`.
- `doubleRootGroupPoints_le_of_restrict_eq`: if `f ≫ χ = α_K` with `α ≠ 0`, then
  `U_{2χ}(K) ⊆ U_{2α_K}(K)`. When `2χ` is not a root, the left side is trivial.
- `doubleRootGroupPoints_commute_of_restrict`: for `α ∈ Φ(S)`, every element of
  `U_{2α_K}(K)` commutes with every element of `U_{α_K}(K)`. When `2α_K` is a root, no
  `n • α_K` with `n ≥ 3` is a root, by `nat_multiple_le_two` over `k`. The Library lemma
  `RelativeRoot.double_subgroup_commute_of_noHigherRoots` then applies, with the
  published `semigroupRealization`, `semigroupCommutator` and `cyclicRootFunctorComparison`.
  Otherwise the double-root group is trivial.

## The lift lemma

`exists_rootJump_lift_of_torusRestrictedJump`: let `α ∈ Φ(S)` and `r : ℝ`. If
`IsRootFiltrationJump (groupHom f ≫ j) ψ α_K r` holds for the torus restriction `ψ` of `φ`,
then there is `χ ∈ relativeRoots j` with `f ≫ χ = α_K` and `IsRootFiltrationJump j φ χ r`.
`IsRootFiltrationJump` is the published predicate `U_{c,y,r} ⊈ U_{c,y,r+} · U_{2c}` of module
`RootJumpLiftNonMultipliable`. The lemma has no hypothesis on `2α`.

The proof is by contradiction. Assume that every root `χ` with `f ≫ χ = α_K` has no jump at
`r`. Take `v ∈ U_{α_K,ψ,r}`; it must be shown to lie in `U_{α_K,ψ,r+} · U_{2α_K}(K)`.

1. By `rootFiltration_torusRestrictedRootFunctionFamily`, `v` lies in the restricted depth
   subgroup `torusRestrictedRootDepthSubgroup hφ f α_K r`, and hence in `U_{α_K}(K)`.
2. `exists_torusRestrictionRootDepth_enumeration` enumerates the roots `a l` of `T` with
   `f ≫ a l = m l • α_K`, `m l > 0`. By
   `RelativeRoot.mem_subgroup_comp_torusHom_iff_existsUnique_rootPointsProduct`, `v` is an
   ordered product of points `X l ∈ U_{a l}(K)`. By
   `mem_torusRestrictedRootDepthSubgroup_iff_coordinate_bounds`, each `X l` has
   `φ`-value at least `m l * r`.
3. By `nsmul_mem_and_le_two_of_restrict_eq`, each `m l` is `1` or `2`. For each `l` there
   are `s > r`, `w` in the restricted depth subgroup at `s`, and `z ∈ U_{2α_K}(K)` with
   `X l = w * z`:
   - If `m l = 1`, then `X l ∈ U_{a l,φ,r}`. Since `a l` has no jump at `r`,
     `X l = w * z` with `φ_{a l}(w) > r` and `z ∈ U_{2 a l}(K) ⊆ U_{2α_K}(K)`
     (`doubleRootGroupPoints_le_of_restrict_eq`). A real `s > r` below `φ_{a l}(w)` comes
     from `exists_gt_forall_le_of_forall_lt`, and
     `filtrationSubgroup_le_torusRestrictedRootDepthSubgroup` places `w` at depth `s`.
   - If `m l = 2`, take `w = 1` and `z = X l ∈ U_{2α_K}(K)`
     (`rootGroupPoints_le_doubleRootGroupPoints_of_restrict_eq_two_nsmul`), with
     `s = r + 1`.
4. A common `s0 > r` below all the `s l` exists (`exists_gt_forall_le_of_forall_lt`), and
   the depth subgroups are antitone. Since `U_{2α_K}(K)` commutes with `U_{α_K}(K)`
   (`doubleRootGroupPoints_commute_of_restrict`), `list_ofFn_prod_mul_of_commute` gives
   `v = (∏ w l) * (∏ z l)`. Here `∏ w l` lies in the restricted depth subgroup at `s0`, so
   its `ψ`-value is at least `s0 > r` by `le_torusRestrictedRootFunctionFamily_iff`.
   Also `∏ z l ∈ U_{2α_K}(K)`. So `v ∈ U_{α_K,ψ,r+} · U_{2α_K}(K)`, which contradicts the
   jump hypothesis.

## The reduction theorem

`unramifiedZeroJumpLiftMultipliable_of_fieldComparison` introduces the binders of
`UnramifiedZeroJumpLiftMultipliableStatement` up to the jump hypothesis `hjump` for `φ x`.
The hypothesis `2 • α ∈ relativeRoots iS` is not used.

1. `hEbase : HasOppositeFactorPairs iS` comes from
   `RelativeRoot.exists_oppositeFactorPair_of_componentReductivity` with the published
   `RelativeRoot.kernelCentralizerComponentReductive`, as in
   `UnramifiedZeroJumpLiftReducedProof`.
2. `hfactor : groupHom f_K ≫ iT_K = iS_K` follows from `hf` by functoriality of base change.
3. The comparison statement is applied at `x` with `φx := φ x` and `ψx` the explicit
   `torusRestrictedRootFunctionFamily` term. Both equations hold by `rfl`. Its forward
   direction turns `hjump` into a jump of `α_K` at `0` for `ψx`, stated for `iS_K`.
   Rewriting with `hfactor` states it for `groupHom f_K ≫ iT_K`.
4. `exists_rootJump_lift_of_torusRestrictedJump` with `K = inertiaFixedField F`, the
   valuation `x.val` and `r = 0` gives the root `χ` of `(G_K, T_K)` that the conclusion
   requires. The conclusion of `UnramifiedZeroJumpLiftMultipliableStatement` is the
   expanded form of `IsRootFiltrationJump iT_K x.val χ 0`.

The theorem is compiled with `set_option maxHeartbeats 1600000`, because the elaboration of
the many base-change instances in the statements is slow.

## Source and provenance

The module is internal: none of its lemmas is a numbered result of Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach* (2023). The jump condition is KP's condition for an affine
functional to be an affine root (Definition 6.3.4, printed pages 217–218, PDF pages
248–249), at a single level. The reduction serves the existence part (1) of KP Proposition
9.4.28 (printed pages 359–360, PDF pages 390–391) for multipliable relative roots. KP prove
9.4.28 through parahoric group schemes. The lift lemma instead uses the Library's
coordinate description of the restricted filtration. It extends the non-multipliable lift
`exists_rootJump_lift_of_two_nsmul_not_mem` (module `RootJumpLiftNonMultipliable`) to all
relative roots. It applies to the torus restriction over the same field `K`, not to the
restriction to `F`-points.
