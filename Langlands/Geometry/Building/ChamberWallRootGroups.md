# Root groups in the direction of a chamber wall

This module identifies the actual chamber root fixer in the derivative
direction of a simple affine root with its affine root group. The fixer
in the reflected chamber is its strict affine root group. The relative
root derivative may be divisible.

## Setting and conclusions

Work over an arbitrary field `k : Type u`, with the existing commutative
group scheme `S`, affine group scheme `G`, monomorphic inclusion
`i : S.toGrp ⟶ G` and actual apartment datum `D : KPApartmentData i ω`.
The only additional structural hypothesis is AS4:
every extended affine root is an affine root or its double is one.
No affine-root-system hypothesis is separately required by these proofs.

Let `psi` be a chamber-simple affine root for a set `C`, let
`a : relativeRoots i`, and assume `psi.linear = rootForm i a`.
The theorem `rootFixer_eq_affineRootGroup_of_simpleAffineRoot` proves

```text
D.rootFixer a C = D.affineRootGroup a psi.
```

For any coroot `v` of `psi`, put
`s = AffineRootSystem.affineReflection psi hv.1`.
The theorem
`rootFixer_reflection_eq_affineRootGroupPlus_of_simpleAffineRoot` proves

```text
D.rootFixer a (s '' C) = D.affineRootGroupPlus a psi.
```

These are equalities of the existing subgroups of `rationalPoints G`,
with the same relative-root direction on both sides. The definition
`rootFixerEquivAffineRootGroup_of_simpleAffineRoot` applies
`MulEquiv.subgroupCongr` to the first equality. Its forward and inverse
maps preserve the underlying rational point.

## Implemented proof

Two preliminary lemmas use a point `x ∈ C` and a wall point
`y ∈ AffineRootSystem.facetClosure D.affineRoots x` with `psi y = 0`.
They require the same derivative equality.

The first, `rootFixer_eq_affineRootGroup_of_mem_facetClosure`, assumes
that `psi` is nonnegative on `C`. Filtration comparison embeds each
element of the chamber root fixer into the depth-zero filtration at `y`.
The existing affine-root-group membership formula identifies this
filtration with the affine root group of `psi`. Conversely, membership
in that affine root group and nonnegativity of `psi` give nonnegative
valuation at every point of `C`, which is the actual root-fixer condition.

The second, `rootFixer_eq_affineRootGroupPlus_of_mem_facetClosure`,
assumes that `C` is a chamber and `psi x < 0`. For a nonidentity root
element, `exists_extendedAffineRoot_of_ne_one` gives a real affine
functional representing its valuation at every apartment point.
That functional and `psi` have the same linear part, so their differences
between `x` and `y` agree. Nonnegative valuation at `x`, together with
`psi x < 0` and `psi y = 0`, gives strictly positive valuation at `y`.
This is precisely membership in the strict affine root group. The identity
element is handled separately. For the converse, positive-depth
filtration comparison transfers strict positivity at `y` to strict
positivity at `x`; filtration constancy on the chamber then gives the
root-fixer condition at every point.

The existing simple-wall geometry supplies the required `x` and `y`.
Positivity of a simple affine root on `C` gives the first equality.
For the second, the coroot reflection fixes `y`, carries chambers to
chambers and negates `psi`. Precomposition of affine roots with this
reflection preserves the root set, so the defining inequalities for the
facet closure show that `y` also belongs to the facet closure of `s x`.
The second preliminary lemma applies to `s '' C`.

## Provenance and scope

This is a derived result from the Library's `ChamberFiltration` and
`AffineIwahoriTitsAssembly` interfaces, their actual filtration and
affine-root-group membership formulas, and their chamber-wall geometry.
It introduces no external mathematical assertion or new axiom.

The module does not assume rank-one factorization, an ordered-root
product theorem, a centralizer-cover comparison or a chamber decomposition.
It establishes the wall-direction fixer equalities only. The full
chamber-simple factorization and the apartment-only
`AffineIwahoriTitsStatement` remain open.
