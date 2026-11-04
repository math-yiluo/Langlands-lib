# Nonidentity normalizers from actual smooth proper quotient geometry

This internal composition works over every algebraically closed field
`k : Type u`, in every characteristic. Let `G` be a smooth affine group, let
`i : T → G` be an actual maximal torus, and let `j : P → G` be a closed
subgroup through which `i` factors by a supplied homomorphism `f`. Assume
`MaximalToriAreConjugate P`. Let `q : G → Q` be a supplied smooth, surjective,
quasi-compact quotient with proper target, whose fibers on every relative
scheme test are exactly the right cosets of the range of `j`.

`nonidentityNormalizerOfNonfixedSmoothProperQuotient` takes an actual rational
lift `g` for which `g ≫ q` is not fixed on all tests by the canonical quotient
action restricted to `T`. It returns an actual rational point in the normalizer
of `T` whose class in the actual relative Weyl group `N(k)/Z(k)` is not one.
It requires no supplied representation or line-stabilizer presentation.

The construction first applies
`HomogeneousQuotient.projectiveEmbeddingData` to the same `j`, `q`, and exact
fiber law. That published construction supplies an actual matrix representation
and the exact coordinate-line stabilizer on all tests. The resulting data are
passed to `nonidentityNormalizerOfWeightSeparatedProperQuotient`. That
construction uses two extreme orbit lines with distinct cocharacter weights
and normalizer representatives to produce the nonidentity Weyl class.
Smoothness of the quotient map supplies its flatness; smoothness of `G`
supplies its local finite type property.

`nonidentityNormalizerOfMovingSmoothProperQuotient` instead takes a rational
torus element `t` and a point `x : V → G` on any relative scheme test such that
left multiplication by the constant image of `t` moves `x ≫ q`. It applies
`Dynamic.nonfixedQuotientLiftOfMovingTestPoint` to produce the required nonfixed
rational lift, then applies the first construction. Properness of `Q`
supplies the separatedness required by that density argument.

The provenance is internal composition of the named Library constructions,
developed by Workers 1549 and 1547. Neither construction assumes that the whole
torus centralizer is contained in `P`, finiteness of the Weyl group, or a
characteristic bound. They retain the actual torus factor, internal conjugacy,
smooth proper exact quotient, and supplied nonfixed section or moving test
point. They do not establish existence of the movement for an arbitrary
prescribed subgroup, a quotient dimension bound, dynamic centralizer
containment, or the unconditional positive-root uniqueness statement.
