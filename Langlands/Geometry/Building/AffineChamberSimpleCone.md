# A chamber is cut out by its simple affine roots

Fix `hΨ : IsAffineRootSystemWithRankZero Ψ` for a set `Ψ` of affine functionals
on a real affine space `A` over `V`, and a regular point `c` (no root vanishes at
`c`, `IsRegular Ψ c`). Write `C = facet Ψ c` for its chamber and
`Π = simpleAffineRoots Ψ C` for the existing set of simple affine roots: the
positive indivisible roots whose hyperplanes are walls of `C` (KP Definition
1.3.19). The vector space and the torsor keep independent universes `uV` and
`uA`.

Source correspondence: Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), remark after Definition 1.3.19 (printed p. 22): "C is uniquely
determined by Ψ(C)⁰, namely as the intersection of the half-spaces `A_{ψ>0}`
for `ψ ∈ Ψ(C)⁰`." The book gives no proof. `facetRel_iff_simple_pos` proves
this statement. The other results (the closure, facets in the closure and
finiteness) are internal deductions with the same proof method. All proofs use
only the existing affine-root, wall-reflection and gallery APIs.

## Definition

`simpleZeroRoots Ψ C x` is the set of simple affine roots of `C` vanishing at
`x`, that is, `{ψ | ψ ∈ simpleAffineRoots Ψ C ∧ ψ x = 0}`.
`mem_simpleZeroRoots` unfolds it.

## Simple walls

`pos_of_mem_simpleAffineRoots` records that a simple root is positive on `C`,
by definition of `positiveRoots`.

`exists_simple_smul_of_mem_wallReflections`: let `ψ₀` be a root with coroot
`v₀` whose reflection is a wall reflection of `c` (`wallReflections Ψ c`). Then
`ψ₀ = r • ψ` for some simple root `ψ ∈ Π` and some real `r`. The existing
`exists_chamberSimple_of_mem_wallReflections` gives a simple root with the same
reflection. `hyperplane_le_of_affineReflection_eq` and
`eq_smul_of_hyperplane_le` turn equality of reflections into proportionality.

## The chamber and its closure

`facetRel_of_simple_pos_of_isRegular`: a regular point `y` with `ψ y > 0` for
all `ψ ∈ Π` lies in `C`. Otherwise some root separates `c` and `y`, and the
existing `exists_wall` gives such a separating root `ψ₀` whose reflection is a
wall reflection of `c`. By the previous lemma `ψ₀ = r • ψ` with `ψ` simple.
Then `ψ₀ c · ψ₀ y = r² ψ(c) ψ(y) ≥ 0`, contradicting separation.

`exists_segment_point` uses local finiteness (`eventually_sign_smul_vadd` and
`exists_pos_of_eventually`). It gives `0 < ε < 1` such that the point
`ε • (c -ᵥ y) +ᵥ y` has the same sign as `y` for every root not vanishing at `y`.
`apply_segment_point` computes an affine functional there as
`ε η(c) + (1 - ε) η(y)`.

`mem_facetClosure_of_simple_pos`: if `ψ y > 0` for all `ψ ∈ Π`, then `y` is in
the closure `facetClosure Ψ c`. The segment point `z` is regular: a root
vanishing at `y` takes the value `ε η(c) ≠ 0` at `z`, and the other roots keep
their sign. All simple roots are positive at `z`, so `z ∈ C` by the previous
lemma. Every root nonzero at `y` has the sign at `y` of its sign at `z`, which
is its sign at `c`.

`isRegular_of_simple_pos`: under the same hypothesis `y` is regular. Suppose a
root `η` vanishes at `y`, and let `r_η` be its reflection, which fixes `y`.
Then `y` lies in the closures of the chambers of `c` and of `r_η c`
(`mem_facetClosure_apply_iff`). The root `η` separates `c` from `r_η c`, so
`exists_wall` gives a separating wall root `ψ₀ = r • ψ` of `c` with `ψ` simple
and `r ≠ 0`. By the existing `root_eq_zero_of_mem_closures`, `ψ₀ y = 0`, hence
`ψ y = 0`, a contradiction.

`facetRel_iff_simple_pos` combines the three lemmas: `y` is in the chamber of
`c` exactly when every simple root is positive at `y`.
`mem_facetClosure_iff_simple_nonneg` proves that `y` is in the closure exactly
when every simple root is nonnegative at `y`. For the converse direction, all
simple roots are positive at the segment point, which therefore lies in `C`.
As before, `y` is then in the closure.

## Facets in the closure

`apply_eq_zero_of_simple_zero_iff`: let `x, y` be in the closure, with the same
simple roots vanishing at both. Then every root `η` vanishing at `x` vanishes at
`y`. Otherwise, choose `t > 0` from `eventually_sign_smul_vadd` at `x` in the
direction `x -ᵥ y`. At `z = t • (x -ᵥ y) +ᵥ x`, a simple root vanishing at `x`
also vanishes at `y`, hence at `z`. A simple root positive at `x` stays
positive. So `z` is in the closure. But `η z = -t η(y)` has the sign opposite
to `η(y)`, which is the sign of `η` on `C`. This contradicts membership of `z`
in the closure.

`facetRel_iff_simple_zero_iff` concludes that points `x, y` of the closure are in
the same facet exactly when the same simple roots vanish at them. Roots
vanishing at one vanish at the other. The remaining roots have the sign they
have at `c` at both points. `facetRel_iff_simpleZeroRoots_eq` states this as
`simpleZeroRoots Ψ C x = simpleZeroRoots Ψ C y`.

## Finiteness

`exists_mem_facetClosure_apply_eq_zero`: the hyperplane of a simple root meets
the closure. The wall clause of `simpleAffineRoots` supplies a face of `C`,
contained in the closure, whose affine span is the hyperplane.

`eq_of_mem_simpleAffineRoots_of_linear_eq`: two simple roots `ψ, η` with the same
derivative are equal. Their difference is a constant `k`. Choose `p` with
`ψ p = 0` and `q` with `η q = 0` in the closure. Nonnegativity of simple roots
on the closure gives `-k = η p ≥ 0` and `k = ψ q ≥ 0`, so `k = 0`.

`finite_simpleAffineRoots`: the derivative map is therefore injective on `Π`
with values in the finite set `derivativeRoots Ψ`, so `Π` is finite.
`finite_chamberSimpleReflections`: each simple root has at most one reflection,
by uniqueness of coroots (`isCoroot_unique`), so the simple reflections
`chamberSimpleReflections Ψ C` form a finite set.

## Scope

These are statements about one chamber of an abstract affine root system with
rank zero allowed. They do not construct faces of `C` for given sets of simple
roots, compare simple reflections with Coxeter components, or concern any
valuation quotient. They prove no witness of
`RootValuationBuildingConstructionStatement`.
