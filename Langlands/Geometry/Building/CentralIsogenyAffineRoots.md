# Actual affine roots and Weyl groups under central-isogeny pullback

This module constructs equivalences of the actual affine-root sets for the
apartment pullback in `CentralIsogenyApartment`. It also proves equality of the
actual affine Weyl groups after conjugation by that apartment equivalence.
These are derived constructions from the existing root groups, filtrations and
affine reflections; no additional literature assertion is introduced.

## Assumptions and direction

The field `k : Type u` has arbitrary universe. Both ambient group schemes `C`
and `G` are affine and locally of finite type. The acting tori `S` and `T` are
split and have monomorphic embeddings `i : S.toGrp ⟶ C` and `j : T.toGrp ⟶ G`.
The inputs are a central isogeny `q : C ⟶ G`, a torus morphism `t : S ⟶ T`
which is an isogeny, and the commuting square
`i ≫ q = CommGroupScheme.groupHom t ≫ j`. The scalar function `ω : kˣ → ℝ`
is arbitrary. The original data are `D : KPApartmentData j ω`.

Write `E` for `D.centralIsogenyPullback q hq hS hT t h ht`, `e` for the actual
point equivalence `D.centralIsogenyApartmentAffineEquiv ...`, and `L` for
`centralIsogenyTranslationEquiv ...`. Thus `e` maps the target-group apartment
`D.Apartment` to the source-group apartment `E.Apartment`, and its derivative
is `L.symm`. No source apartment axioms are premises.

## Functionals and actual root groups

`affineFunctionalCentralIsogenyPullbackEquiv` is the linear equivalence
`F(ψ) = ψ ∘ e.symm`. It evaluates to `ψ(x)` at `e(x)`. Its derivative at a
source translation `v` is `ψ.linear (L v)`. The established root-form comparison
therefore proves that this derivative is the source form of the restricted
root `t ≫ a` exactly when `ψ.linear` is the target form of `a`. Adding any real
constant commutes with `F`.

`mem_filtration_centralIsogenyPullback_iff` expresses membership in the source
filtration at `e(x)` as membership in the source root group together with
membership of the `q`-image in the original target filtration at `x`.
`mem_affineRootGroup_centralIsogenyPullback_iff` applies this equivalence at every
point. Surjectivity of the actual root-point multiplicative equivalence gives
`map_affineRootGroup_centralIsogenyPullback`: the source affine root group maps
onto the original target affine root group.

The strict group is the union over positive constants added to the affine
functional. Commutation with those constants proves the analogous restricted
membership formula and exact image equality for `affineRootGroupPlus`.
The retained source root-group condition is essential: the argument uses no
injectivity or surjectivity assertion on ambient rational points.

## Doubling and noncontainment

`map_doubleRootGroupPoints_centralIsogenyPullback` compares the actual convention
`U_(2a) = {1}` when `2a` is not a relative root. Character restriction commutes
with doubling, and the established root-support equivalence preserves and
reflects membership of `2a`. In the root case the root-point equivalence gives
the exact image; in the other case both groups are the identity subgroup.

The map on rational points is injective on each relevant source root group,
by its restricted multiplicative equivalence. The strict affine root group
lies in that root group. The doubled-root group does too, by the positive-
multiple subgroup inclusion imported from `RootSubgroupMultipleInclusion`.
Their set product consequently lies in the same root group.

`affineRootGroup_subset_mul_centralIsogenyPullback_iff` uses this restricted
injectivity to reflect containment of the affine root group in the product
of the strict group and the doubled-root group. Images commute with the set
product, and the preceding exact-image formulas identify both sides with
the original target containment. This proves the noncontainment comparison
in the existing definition of ordinary affine roots.

## Affine-root equivalences and Weyl conjugation

An extended affine root has a relative-root derivative and a strict group
unequal to its affine root group. Restricted injectivity reflects equality
of these groups; applying the point map preserves equality in the other
direction. The root-support equivalence identifies every possible derivative.
`mem_extendedAffineRoots_centralIsogenyPullback_iff` follows.

For ordinary affine roots the same derivative comparison combines with the
product-containment equivalence. This gives
`mem_affineRoots_centralIsogenyPullback_iff`. Restricting `F` to the corresponding
subtypes defines `extendedAffineRootsCentralIsogenyPullbackEquiv` and the entry
`affineRootsCentralIsogenyPullbackEquiv`.

`transportedRoots_centralIsogenyPullback` states the exact set equality:
`AffineRootSystem.transportedRoots e D.affineRoots = E.affineRoots`.
The final theorem `map_affineWeylGroup_centralIsogenyPullback` applies the generic
reflection-conjugation theorem from `AffineWeylTransport`. Conjugation
`g ↦ e ∘ g ∘ e.symm` maps `affineWeylGroup D.affineRoots` onto
`affineWeylGroup E.affineRoots`. This is an equality of the groups generated
by the existing affine reflections, including when the root sets are empty.

## Scope

The module supplies a comparison for the given torus square; it does not
construct such a square for a simply connected cover. It proves no V7,
full-centralizer V6 or source AS5 assertion. It does not prove that a source
normalizer image is its affine Weyl group, or the final statement
`SimplyConnectedNormalizerAffineWeylStatement`. These remain separate
obligations, with the final statement's premises unchanged.
