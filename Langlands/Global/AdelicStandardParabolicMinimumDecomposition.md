# Actual decompositions of standard-parabolic height minima

Author: Worker 83.

This derived prerequisite constructs the Levi-unipotent factorization used
by the normalized tail-minimum interface. It also combines the actual
Iwasawa property, successive rational minima and compact height transport
to construct such normalized data for a right rational translate of every
ambient norm-one point. All constructions use the supplied actual compact
subgroup and the canonical standard subgroup schemes.

Fix an arbitrary universe `u`, number field `F : Type u`, affine group
scheme `G` over `Spec F`, commutative group scheme `T`,
`i : T.toGrp ⟶ G`, and cocharacter `ν`. Assume that `G` is connected
reductive, `i` is a maximal split torus and `ν` is generic whenever the
theorems below invoke the valid standard-family setup.

## Parabolic points have the required ordered factors

`exists_standardLevi_mul_standardUnipotent_of_mem_range` takes a valid root
subset `J` and any actual adelic point in the canonical `P_J` image. It
constructs actual points `h` of the canonical `L_J` and `x` of the canonical
`U_J` with

`p = image(h) image(x)`.

The proof evaluates canonical representability on the actual adele-algebra
test scheme. The published standard-cocharacter theorem supplies an actual
standard cocharacter realizing the Levi and unipotent subgroup functors.
The published all-test dynamic decomposition gives `p = v l`.
Conjugating `v` by `l⁻¹` produces a point of the same unipotent subgroup,
since `l⁻¹` belongs to the standard parabolic. Thus

`p = l (l⁻¹ v l)`.

Canonical representability lifts the two factors to the actual canonical
Levi and unipotent group schemes. The proof assumes no norm-one condition
on `p` or either factor.

## Normalized tail data directly from a parabolic minimum point

`HasNormalizedStandardParabolicTailMinima` is a Prop-valued predicate
asserting the displayed ordered factorization together with
`HasNormalizedStandardLeviTailMinima` for the raw Levi factor. Its latter
data contain a constructed split component factoring through the fixed
torus, an actual intrinsic positive factor, and a norm-one Levi point
satisfying the successor inequalities over its intrinsic preceding
standard parabolics.

For a valid family `K : ℕ → Set (characterLattice T)`,
`hasNormalizedStandardParabolicTailMinima_of_mem_range` proves this
predicate for each ambient norm-one `p` in the actual `P_(K 0)` image that
satisfies the first `s+1` minimum inequalities over the ambient preceding
parabolic intersections. Every representation has a selected coordinate
line preserved on all scheme tests by its individual canonical parabolic.
The proof constructs the ordered factors by the preceding theorem and
applies the normalized canonical-Levi restriction theorem. The constant
`c` is unchanged and can be any real number.

## Uniform minima after Iwasawa decomposition

`isParabolicIwasawaCompact_standard_of_minimal` transfers the given
minimal-parabolic Iwasawa property to every valid `P_J` using the same
compact subgroup. The published parabolic-order theorem gives
`P_empty ≤ P_J` on all scheme tests. Evaluating on the adele-algebra test
and using canonical representability enlarges the parabolic factor in
the given coverage, while preserving the supplied subgroup's compactness
and maximality. Thus the next theorem applies to the minimal-parabolic
Iwasawa predicate appearing in the chamber task.

`exists_iwasawa_normalized_standardLevi_tail_minima` takes the same valid
setup and representations, a subgroup `C` of the actual adelic group, and
the existing predicate `IsParabolicIwasawaCompact` for `P_(K 0)` and `C`.
For each fixed finite prefix `s+1`, it constructs `D > 0`, independent of
the point, such that every `g ∈ G(A_F)^1` has

`g · rational(q) = k p`, with `k ∈ C` and `p ∈ G(A_F)^1`,

where `p` satisfies all first `s+1` minimum inequalities with constant `D`
and has `HasNormalizedStandardParabolicTailMinima` with that same constant.
The coordinate indices force positive dimensions; no separate dimension
hypothesis is needed.

The proof first applies the existing successive-minima theorem with
constant one. All-test parabolic line preservation supplies the required
affine unit-scalar action on the individual subgroup ranges. Apply the
given `P C` coverage to the inverse of the resulting minimum point and
invert its factorization. This gives the required compact factor on the
left, with its inverse still in the same supplied subgroup `C`.

Compactness makes every `C` point norm one. Removing this factor from the
ambient norm-one point therefore gives an ambient norm-one parabolic
point. The published compact height-transport theorem supplies the uniform
positive constant `D` for all representations in the finite prefix and
transfers the minimum inequalities to this parabolic factor. Finally the
preceding theorem constructs its normalized Levi tail data.

The result retains the supplied compact subgroup. It neither assumes
compactness of the rational quotient nor chooses a different Iwasawa
subgroup. The family `K a` need not be nested, roots need not be nonempty,
and `s=0` is included. No faithfulness or exact stabilizer premise is added
to line preservation.

## Provenance and remaining obligations

These are internal consequences of the imported canonical standard-family,
actual orbit-height, compact-transport, and normalized-Levi theorems.
There is no new external-source assertion. The only Iwasawa premise is the
existing actual predicate for the supplied compact subgroup and actual
first standard parabolic.

The conclusion supplies a starting point for rank induction. It does not
bound the extracted positive factors by simple roots, prove the rank-one
height estimates, complete the induction, or establish
`AdelicSiegelChamberReductionStatement`.
